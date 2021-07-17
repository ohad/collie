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
record Command where
  constructor MkCommand
  name        : String
  description : String
  subcommands : Fields Command
  modifiers : Fields Modifier
  arguments : Arguments

public export
basic : {arg : String} -> Arguments -> Command
basic args = MkCommand
  { name = arg
  , description = ""
  , subcommands = []
  , modifiers   = []
  , arguments   = args
  }

public export
data ParsedCommand : (c : Command) -> Type where
  Here :
    (parsedMods : ParsedModifiers mods) ->
    (ParsedArgs : ParsedArguments args) ->
    ParsedCommand (MkCommand cmdName descr subs mods args)
  There :
    (pos : Any p cs) ->
    (parsedSub : ParsedCommand $ field pos) ->
    ParsedCommand (MkCommand cmdName descr cs mods args)

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

-- Logic ought to be shared logic with Modifiers.update
{-
public export
updateArgument : {ducer : Parseducer} -> (ps : ParsedArguments ducer) ->
  String -> Error $ ParsedArguments ducer
updateArgument (Some d ** parser)  p Nothing _ = throwE "Too many arguments: only one expected"
updateArgument (Some d ** parser)  p (Just y) x = Just <$> p x
updateArgument (ALot ds ** parser) p ps x = let _ = openMagma $ Maybe.rawMagma ds in
  do
  p <- p x
  pure (Just p <+> ps)
-}


{-
public export
updateArgument : (d : Domain) -> (p : Parser d) -> (ps : ParsedArguments (d ** p)) ->
  String -> Error $ ParsedArguments (d ** p)
updateArgument (Some d ) p Nothing _ = throwE "Too many arguments: only one expected"
updateArgument (Some d ) p (Just y) x = Just <$> p x
updateArgument (ALot ds) p ps x = let _ = openMagma $ Maybe.rawMagma ds in
  do
  p <- p x
  pure (Just p <+> ps)

public export
parseArguments : (p : (d : Domain ** Parser d)) -> List String
  -> ParsedArguments p -> Error $ ParsedArguments p
parseArguments p str dft = foldl (cons p) (pure dft) str
  where
  cons : (p : (d : Domain ** Parser d)) ->
    Error (ParsedArguments p) -> String -> Error (ParsedArguments p)
  cons p@(d ** parser) result str = do
    Just v <- result
    | Nothing => pure <$> parser str
    let ALot ds = d
      | Some _ => throwE "Too many arguments: only one expected."
    w <- parser str
    pure let _ = openMagma ds in
      Just (v <+> w)

public export 0
ModifierRecordTabs : {0 arg : String} -> (pos : arg `Elem` args) -> Type
ModifierRecordTabs {arg} _ = Modifier arg

public export 0
DummyRecordTabs : {0 arg : String} -> (pos : arg `Elem` args) -> Modifier arg -> Type
DummyRecordTabs {arg} pos = ParsedModifier {arg}

public export
DUMMY : (args : ArgList) -> (mods : RECORD args (TABULATE args ModifierRecordTabs)) ->
  RECORD args (TypeFIELDS args $ MAP {args} DummyRecordTabs mods)
DUMMY      []                    mods  = ()
DUMMY (arg :: args) (MkFlag   _, mods) = (False, DUMMY args mods)
DUMMY (arg :: args) (MkOption _, mods) = (Nothing, DUMMY args mods)

public export
dummy : {args : ArgList} -> {mods : Record args (tabulate ModifierRecordTabs)} ->
  Record args (TypeFields $ map (\pos => DummyRecordTabs pos) mods)
dummy {args} {mods} = MkRecord $ DUMMY args mods.content

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
