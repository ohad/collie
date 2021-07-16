module Collie.Parser

import Data.List
import Data.String
import Data.Either
import Data.Maybe
import Data.Fun
import Data.Record.Ordered
import Collie.Core

{-
hack : {f, g : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (0 prf : (arg : String) -> (pos : arg `Elem` args) -> f pos = g pos) ->
  Ordered.tabulate f = Ordered.tabulate g
-}

public export
parseSubCommand : (cmd : Command arg) -> {x : String} -> List String ->
  {auto pos : x `Elem` cmd.subcommands.fst} -> Error $ ParsedCommand cmd

public export
parseCommand : (cmd : Command arg) -> List String -> Error $ ParsedCommand cmd

parseSubCommand (MkCommand description (Evidence subs cs.commands) modifiers arguments) xs
  = (\s => SubCommand pos s) <$> (parseCommand (cs.project' x) xs)

parseCommand (MkCommand description subcommands (names ** mods) arguments) []
  = do
  x <- parseArguments arguments [] ?h2
  pure $ TheCommand (let v = dummy {args = names} in ?h1391)
    {- `dummy` ought to go here, but I'm having rewriting hell at the moment :(
    -} x
parseCommand (MkCommand description subcommands (names ** mods) arguments) ("--" :: xs)
  = do x <- parseArguments arguments xs ?h23
       pure $ TheCommand ?parseCommand_rhs_1 x
parseCommand cmd (x :: []) = ?parseCommand_rhs_2
parseCommand cmd (x :: y :: xs) = ?parseCommand_rhs_3

   v : {mods : Record names (MkFields {Args = names} (TABULATE   names (\{arg:920} : String => ModifierRecordTabs {{neq:838} = #} {args = names} {arg})))} -> Record names (MkFields {Args = names} (TypeFIELDS names (MAP {args = names} {srcs = (\0 arg, pos => Modifier arg)} {tgts = (\0 arg, pos => Type)} (\0 {arg:1690} : String, pos : Elem {a = String} {neq = #} arg names => ParsedModifier {arg}) (.content {args = names} {flds = MkFields {Args = names} (TABULATE names (\{arg:1659} : String, pos => Modifier arg))} mods))))
h1391 :        Record names (MkFields {Args = names} (TypeFIELDS names (MAP {args = names} {srcs = (\0 arg, pos => Modifier (.recall {a = String} {x = arg} {neq = #} names pos))} {tgts = (\0 arg, pos => Type)} (\0 {arg:1690} : String, {_:2417} : Elem {a = String} {neq = #} arg names => ParsedModifier {arg = .recall {a = String} {x = arg} {neq = #} names _}) (.content {args = names} {flds = MkFields {Args = names} (TABULATE names (\{arg:1659} : String, pos => Modifier (.recall {a = String} {x = arg} {neq = #} names pos)))} mods))))
