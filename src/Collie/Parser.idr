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
