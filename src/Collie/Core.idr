module Collie.Core

import public Collie.Options.Domain
import public Collie.Options.Usual
import public Collie.Modifiers
import public Data.Record
import public Data.Record.SmartConstructors

import public Data.Vect
import public Data.DPair
import public Data.Magma

import public Syntax.WithProof

import public Decidable.Decidable
import public Decidable.Decidable.Extra1

%default total

public export
record Command (name : String) where
  constructor MkCommand
  description : String
  subcommands : Fields Command
  modifiers : Fields Modifier
  arguments : Arguments

public export
basic : {cmdName : String} ->
        (description : String) -> Arguments -> Command cmdName
basic desc args = MkCommand
  { description = desc
  , subcommands = []
  , modifiers   = []
  , arguments   = args
  }

public export
data Any : (p : (0 nm : String) -> Command nm -> Type) ->
           {0 nm : String} -> (cmd : Command nm) -> Type where
  Here : {0 p : (0 nm : String) -> Command nm -> Type} ->
         p nm cmd -> Any p cmd
  There :
    {c : String} ->
    (pos : c `IsField` cmd.subcommands) ->
    (parsedSub : Any p (snd $ field pos)) ->
    Any p cmd

namespace Any

  public export
  map : {0 p, q : (0 nm : String) -> Command nm -> Type} ->
        {cmd : Command nm} ->
        ({0 nm : String} -> (cmd : Command nm) -> p nm cmd -> q nm cmd) ->
        Any p cmd -> Any q cmd
  map f (Here pcmd) = Here (f _ pcmd)
  map f (There pos p) = There pos (map f p)

  public export
  traverse : Applicative m =>
      {0 p, q : (0 nm : String) -> Command nm -> Type} ->
      {cmd : Command nm} ->
      ({0 nm : String} -> (cmd : Command nm) -> p nm cmd -> m (q nm cmd)) ->
      Any p cmd -> m (Any q cmd)
  traverse f (Here pcmd)   = Here <$> f _ pcmd
  traverse f (There pos p) = There pos <$> traverse f p

public export
record ParsedCommandT
       (f, g : Type -> Type)
       (0 nm : String) (cmd : Command nm) where
  constructor MkParsedCommandT
  modifiers : ParsedModifiersT f g cmd.modifiers
  arguments : ParsedArgumentsT g cmd.arguments

public export
record ParsedCommand
       (0 nm : String) (cmd : Command nm) where
  constructor MkParsedCommand
  modifiers : ParsedModifiers cmd.modifiers
  arguments : ParsedArguments cmd.arguments

namespace ParsedCommand

  public export
  defaulting : {cmd : Command nm} ->
    ParsedCommandT Maybe f nm cmd -> ParsedCommandT Prelude.id f nm cmd
  defaulting (MkParsedCommandT mods args)
    = MkParsedCommandT (defaulting mods) args

  public export
  finalising : {cmd : Command nm} ->
    ParsedCommandT Maybe Maybe nm cmd -> Error (ParsedCommand nm cmd)
  finalising (MkParsedCommandT mods args)
    = MkParsedCommand
    <$> finalising mods
    <*> finalising MissingArgument _ args

public export
ParseTreeT : (f, g : Type -> Type) -> (cmd : Command nm) -> Type
ParseTreeT f g = Any (ParsedCommandT f g)

public export
ParseTree : (cmd : Command nm) -> Type
ParseTree = Any ParsedCommand

namespace ParsedTree

  public export
  defaulting : {cmd : Command nm} ->
    ParseTreeT Maybe f cmd -> ParseTreeT Prelude.id f cmd
  defaulting = map (\ _ => defaulting)

  public export
  finalising : {cmd : Command nm} ->
    ParseTreeT Maybe Maybe cmd -> Error (ParseTree cmd)
  finalising = traverse (\ _ => finalising)

public export
lookup : {nm : String} -> {c : Command nm} -> Any p c -> (nm ** Command nm)
lookup (Here {}) = (_ ** c)
lookup (There {parsedSub, _}) = lookup parsedSub

{-
  Some agda syntax magic goes here, so that:

    [ descr ::= mods & args ]
  desugars into
    TheCommand {descr} mods args
  and
    descr [ pos ] sub
  desugars into
    SubCommand {sub = desc} pos sub

  These can't be just smart constructors though, since they're meant
  to appear in patterns, I think.
-}

public export
(.update) : {arg : Arguments} -> (ps : ParsedArgumentsT Maybe arg) ->
  String -> Error $ ParsedArgumentsT Maybe arg
(.update) {arg = MkArguments _ (Some d ) parser} (Just _) _
  = throwE TooManyArguments
(.update) {arg = MkArguments _ (Some d ) parser} Nothing x
  = fromEither $ bimap CouldNotParse Just (parser x)
(.update) {arg = MkArguments _ (ALot ds) parser} old     x
  = let _ = openMagma $ Maybe.rawMagma ds
  in do
    p <- fromEither $ bimap CouldNotParse Just $ parser x
    pure (old <+> p)

public export
(.parse) : (args : Arguments) ->
  (old : ParsedArgumentsT Maybe args) ->
  List String ->
  Error $ ParsedArgumentsT Maybe args
args.parse old = foldl (\u,s => do {acc <- u; acc.update s}) (pure old)

public export
initParsedCommand : {cmd : Command nm} -> ParsedCommandT Maybe Maybe nm cmd
initParsedCommand = MkParsedCommandT initNothing Nothing
