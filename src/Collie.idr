||| Collie: Command line interface for Idris2 applications
|||
||| Based on Guillaume Allais's agdARGS library:
|||
||| https://github.com/gallais/agdargs/
module Collie

import public Collie.Options.Domain
import public Collie.Options.Usual
import public Collie.Modifiers
import public Data.Record.Ordered
import public Data.Record.Ordered.SmartConstructors
import public Data.Record.Ordered.Properties

import public Data.Vect
import public Data.DPair
import public Data.Magma

%default total

public export
ParsedArgument : (d : Domain ** Parser d) -> Type
ParsedArgument (d ** p) = Carrier d

public export
ParsedArguments : (d : Domain ** Parser d) -> Type
ParsedArguments (d ** p) = Maybe $ Carrier d

public export
data Command : (name : String) -> Type

public export
SubCommands : Type

public export
data Commands : (names : ArgList) -> Type

public export 0
CommandRecordTabs : {0 arg : String} -> (pos : arg `Elem` args) -> Type
CommandRecordTabs {arg} _ = Command arg

public export
record Command (name : String) where
  constructor MkCommand
  description : String
  subcommands : SubCommands
  modifiers : Modifiers
  arguments : Arguments

SubCommands = Exists \names => Commands names

public export
record Commands (Names : ArgList) where
  constructor (.commands)
  cols : Record Names (tabulate CommandRecordTabs)

public export
noSubCommands : SubCommands
noSubCommands = Evidence _ [].commands

public export
basic : {arg : String} -> Arguments -> Command arg
basic args = MkCommand
  { description = arg
  , subcommands = noSubCommands
  , modifiers   = noModifiers
  , arguments   = args
  }

public export
record CLI where
  constructor MkCLI
  name : String
  exec : Command name

public export
data ParsedCommand : (c : Command arg) -> Type where
  TheCommand :
    {0 descr : String} -> {subs : SubCommands} ->
    {0 modNames : ArgList} ->
    {0 mods : Record modNames Modifiers.toFields} ->
    (parsedMods : ParsedModifiers mods) ->
    {args : (d : Domain ** Parser d)} ->
    (ParsedArgs : ParsedArgument args) ->
    ParsedCommand (MkCommand descr subs (modNames ** mods) args)

  SubCommand :
    {0 descr : String} -> {0 sub : String} -> {0 subs : ArgList} ->
    (pos : sub `Elem` subs) -> {cs : Record subs $ tabulate CommandRecordTabs} ->
    {mods : (names : ArgList ** Record names Modifiers.toFields)} ->
    (parsedSub : ParsedCommand $ cs.project' {flds = CommandRecordTabs} sub {pos}) ->
    {args : (d : Domain ** Parser d)} ->
    ParsedCommand (MkCommand descr (Evidence subs cs.commands) mods args)

public export
ParsedInterface : CLI -> Type
ParsedInterface iface = ParsedCommand (exec iface)

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
updateArgument : (d : Domain) -> (p : Parser d) -> (ps : ParsedArguments (d ** p)) ->
  String -> Error $ ParsedArguments (d ** p)
updateArgument (Some d ) p Nothing _ = throwE "Too many arguments: only one expected"
updateArgument (Some d ) p (Just y) x = Just <$> p x
updateArgument (ALot ds) p ps x = let _ = openMagma $ Maybe.rawMagma ds in
  do
  p <- p x
  pure (Just p <+> ps)

public export
parserArguments : (p : (d : Domain ** Parser d)) -> List String
  -> ParsedArguments p -> Error $ ParsedArguments p
parserArguments p str dft = foldl (cons p) (pure dft) str
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
