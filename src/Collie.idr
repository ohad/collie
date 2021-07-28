||| Collie: Command line interface for Idris2 applications
|||
||| Based on Guillaume Allais's agdARGS library:
|||
||| https://github.com/gallais/agdargs/
module Collie

import public Collie.Core
import public Collie.Parser
import public Collie.Usage

import public Collie.Options.Domain
import public Collie.Options.Usual
import public Collie.Modifiers
import public Data.Record.Ordered
import public Data.Record.Ordered.SmartConstructors
import public Data.Record.Ordered.Properties


import public Data.Vect
import public Data.DPair
import public Data.Magma

import public Data.SnocList

import public System

public export
(.parseArgs) : (cmd : Command nm) -> HasIO io =>
  io (String `Either` ParseTree Prelude.id Maybe cmd)
cmd.parseArgs = do
  args <- getArgs
  let args' =
        case args of
          [] => []
          _ :: xs => xs
  -- putStrLn "parsing arguments: \{show $ cmd.name :: args'}"
  pure $ map defaulting $ runIdentity $ runEitherT $ parse cmd args'


infixr 4 -=->

public export
0 (-=->) : (Command arg) -> Type -> Type
(-=->) cmd a =
  {0 covers : ParseTree Prelude.id Maybe cmd} ->
  {path : List String} ->
  {focus : _} -> {focusCmd : _} ->
  {parsed : ParsedCommand Prelude.id Maybe focus focusCmd } ->
  IsPathTo covers path parsed ->
  a

public export
(.withArgs) : {nm : String} -> (cmd : Command nm) -> (cmd -=-> IO a) -> IO a
cmd .withArgs k
  = do Right args <- cmd.parseArgs
         | _ => do putStrLn (cmd .usage)
                   exitFailure
       let (MkFocus sub path) = focus args
       k path
