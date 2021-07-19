module Collie.Core

import public Collie.Options.Domain
import public Collie.Options.Usual
import public Collie.Modifiers
import public Data.Record.Ordered
import public Data.Record.Ordered.SmartConstructors
import public Data.Record.Ordered.Properties

import public Data.Vect
import public Data.DPair
import public Data.Magma

import public Syntax.WithProof

%default total

public export
ParsedArgument : Arguments -> Type
ParsedArgument ducer = Carrier ducer.domain

public export
ParsedArguments : (f : Type -> Type) -> Arguments -> Type
ParsedArguments f ducer = f $ Carrier ducer.domain

public export
record Command where
  constructor MkCommand
  name        : String
  description : String
  subcommands : Fields Command
  modifiers : Fields Modifier
  arguments : Arguments

public export
basic : (arg : String) -> Arguments -> Command
basic cmdName args = MkCommand
  { name = cmdName
  , description = ""
  , subcommands = []
  , modifiers   = []
  , arguments   = args
  }

public export
data Any : (p : Command -> Type) -> (cmd : Command) -> Type where
  Here : p cmd -> Any p cmd
  There :
    (pos : c `IsField` cmd.subcommands) ->
    (parsedSub : Any p (field pos)) ->
    Any p cmd

namespace Any

  public export
  map : {cmd : Command} -> ((cmd : Command) -> p cmd -> q cmd) ->
    Any p cmd -> Any q cmd
  map f (Here pcmd) = Here (f _ pcmd)
  map f (There pos p) = There pos (map f p)

public export
record ParsedCommand (f, g : Type -> Type) (cmd : Command) where
  constructor MkParsedCommand
  modifiers : ParsedModifiers f g cmd.modifiers
  arguments : ParsedArguments g cmd.arguments

namespace ParsedCommand

  public export
  defaulting : {cmd : Command} ->
    ParsedCommand Maybe f cmd -> ParsedCommand Prelude.id f cmd
  defaulting (MkParsedCommand mods args)
    = MkParsedCommand (defaulting mods) args

public export
ParseTree : (f, g : Type -> Type) -> (cmd : Command) -> Type
ParseTree f g = Any (ParsedCommand f g)

namespace ParsedTree

  public export
  defaulting : {cmd : Command} ->
    ParseTree Maybe f cmd -> ParseTree Prelude.id f cmd
  defaulting = map (\ _ => defaulting)

public export
lookup : {c : Command} -> Any p c -> Command
lookup (Here {}) = c
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
(.update) : {arg : Arguments} -> (ps : ParsedArguments Maybe arg) ->
  String -> Error $ ParsedArguments Maybe arg
(.update) {arg = MkArguments (Some d ) parser} (Just _) _
  = throwE "Too many arguments: only one expected"
(.update) {arg = MkArguments (Some d ) parser} Nothing x = Just <$> parser x
(.update) {arg = MkArguments (ALot ds) parser} old     x
  = let _ = openMagma $ Maybe.rawMagma ds
  in do
    p <- parser x
    pure (old <+> Just p)

public export
(.parse) : (args : Arguments) ->
  (old : ParsedArguments Maybe args) ->
  List String ->
  Error $ ParsedArguments Maybe args
args.parse old = foldl (\u,s => do {acc <- u; acc.update s}) (pure old)

public export
initParsedCommand : {cmd : Command} -> ParsedCommand Maybe Maybe cmd
initParsedCommand = MkParsedCommand initNothing Nothing
