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
castGen : (name : a -> String) -> (sx : SnocList a) ->
  {auto 0 fresh : Fresh {neq = (#) `on` Builtin.fst}
                  (map (\u => (name u, u)) sx) } ->
  Fields a
castGen name sx = cast (map (\u => (name u, u)) sx)

public export
MkCommands : (sx : SnocList Command) ->
  {auto 0 fresh : Fresh {neq = (#) `on` Builtin.fst}
                  (map (\u => (u.name, u)) sx) } ->
  Fields Command
MkCommands = castGen name

public export
(.withArgs) : (cmd : Command) -> HasIO io =>
  io (String `Either` ParseTree Prelude.id Maybe cmd)
cmd.withArgs = do
  args <- getArgs
  let args' =
        case args of
          [] => []
          _ :: xs => xs
  -- putStrLn "parsing arguments: \{show $ cmd.name :: args'}"
  pure $ map defaulting $ runIdentity $ runEitherT $ parse cmd args'
