module Collie.Parser

import Data.List
import Data.String
import Data.Either
import Data.Maybe
import Data.Fun
import Data.Record.Ordered
import Collie.Core

public export
parseCommand : (cmd : Command nm) -> List String ->
  ParsedCommandT Maybe Maybe nm cmd -> Error (ParsedCommandT Maybe Maybe nm cmd)

public export
parseModifier : (cmd : Command nm) -> {modName : String} ->
  (pos : modName `IsField` cmd.modifiers) -> (rest : List String) ->
  ParsedCommandT Maybe Maybe nm cmd ->
  (factory : ParsedModifierT Prelude.id Prelude.id (snd $ field pos) ->
             Error (ParsedModifiersT Maybe Maybe cmd.modifiers)) ->
  Error (ParsedCommandT Maybe Maybe nm cmd)

parseCommand cmd [] old = pure old
parseCommand cmd ("--" :: xs) old = do
  u <- cmd.arguments.parse old.arguments xs
  pure $ record { arguments = u} old

parseCommand cmd (x :: xs) old
  = case x `isField` cmd.modifiers of
      No  _   => do u <- old.arguments.update x
                    parseCommand cmd xs $ record { arguments = u} old
      Yes pos => parseModifier cmd pos xs old (old.modifiers.update pos)

parseModifier  cmd pos rest old factory with (snd $ field pos)
 parseModifier cmd pos rest old factory | MkFlag   flg = do
    mods <- factory True
    parseCommand cmd rest $ record { modifiers = mods } old
 parseModifier cmd pos rest old factory | MkOption opt
   = case rest of
       []      => throwE (MissingOptArg modName)
       x :: xs => do args <- (opt.project "arguments").parser x
                     mods <- factory args
                     parseCommand cmd xs $ record {modifiers = mods} old

public export
parse : (cmd : Command nm) -> List String -> Error $ ParseTreeT Maybe Maybe cmd
parse cmd [] = pure (Here initParsedCommand)
parse cmd xs@("--" :: _) = Here <$> parseCommand cmd xs initParsedCommand
parse cmd ys@(x :: xs) = case x `isField` cmd.subcommands of
                           Yes pos => There pos <$> parse (snd $ field pos) xs
                           No  _   => Here <$> parseCommand cmd ys initParsedCommand
