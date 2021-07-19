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
ParsedArguments : Arguments -> Type
ParsedArguments ducer = Maybe $ Carrier ducer.domain

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
    (pos : c `IsField` cmd.subcommands) ->
    (parsedSub : Any p (snd $ field pos)) ->
    Any p cmd

public export
record ParsedCommand (0 nm : String) (cmd : Command nm) where
  constructor MkParsedCommand
  modifiers : ParsedModifiers cmd.modifiers
  arguments : ParsedArguments cmd.arguments

public export
ParseTree : (cmd : Command nm) -> Type
ParseTree = Any ParsedCommand

public export
lookup : {nm : String} -> {c : Command nm} -> Any p c -> (nm ** Command nm)
lookup (Here {}) = (_ ** c)
lookup (There {parsedSub, _}) = lookup parsedSub

{-
  Some agda syntax magic goes here, so that:

    [ descr ::= mods & args ]
  desugras into
    TheCommand {descr} mods args
  and
    descr [ pos ] sub
  desugars into
    SubCommand {sub = desc} pos sub

  These can't be just smart constructors though, since they're meant
  to appear in patterns, I think.
-}

public export
(.update) : {arg : Arguments} -> (ps : ParsedArguments arg) ->
  String -> Error $ ParsedArguments arg
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
  (old : ParsedArguments args) ->
  List String ->
  Error $ ParsedArguments args
args.parse old = foldl (\u,s => do {acc <- u; acc.update s}) (pure old)

public export
initNothing : {flds : Fields a} -> Record (Maybe . f) flds
initNothing = MkRecord $ tabulate (\_ => Nothing)

public export
initParsedCommand : {cmd : Command nm} -> ParsedCommand nm cmd
initParsedCommand = MkParsedCommand initNothing Nothing

-- TODO: Come back to here later
{-
public export
parseModifier : {c : Command} -> (pos : Any p c.modifiers) ->
  (recyxs : ParsedCommand c) -> Error $ ParsedCommand c
parseModifier pos (There pos' parsedSub)
  = throwE $ "Found a {TODO: print modifier in (field pos')} for command \{c.name} " ++
             "with subcommand \{parsedSub.deref.name}"
parseModifier pos (Here parsedMods parsedArgs) =
  (\m => Here m parsedArgs) <$> (parsedMods.update
-}


{-
public export
parseModifier : {arg : String} -> (c : Command arg) -> {x : String} ->
  (recyxs, recxs : Error (ParsedCommand c)) ->
  (pos : x `Elem` c.modifiers.fst) -> Error $ ParsedCommand c
parseModifier (MkCommand description (Evidence names cs.commands) (args ** mods) arguments)
  {x} recyxs recxs pos = do
  TheCommand mods' args <- recyxs
  | SubCommand _ _ => throwE $ "Found a MkFlag for command \{arg} " ++
                               "with subcommand \{description}"
  p <- case @@(the (Modifier _) $ mods.project' x {pos}) of
        (MkFlag   flg ** prf) => pure $ replace {p = ParsedModifier} (sym prf) $
                                        True
        (MkOption opt ** prf) => do
          u <- (opt.project "arguments").snd x
          pure $ replace {p = ParsedModifier} (sym prf)
               $ Just u
  (\m => TheCommand m args) <$> (mods'.update x p)

public export
parseArgument : {arg : String} -> (c : Command arg) -> Error (ParsedCommand c) ->
  String -> Error $ ParsedCommand c
parseArgument (MkCommand description (Evidence names cs.commands) (args ** mods) (d ** p))
  recyxs x = do
  TheCommand mods' args' <- recyxs
  | SubCommand _ _ => throwE $ "Found an argument for command \{arg} " ++
                               "with subcommand \{description}"
  TheCommand mods' <$> updateArgument d p args' x
-}
