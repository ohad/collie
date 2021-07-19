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
(.withArgs) : (cmd : Command nm) -> HasIO io => io (String `Either` ParseTree cmd)
cmd.withArgs = do
  args <- getArgs
  let args' =
        case args of
          [] => []
          _ :: xs => xs
  -- putStrLn "parsing arguments: \{show $ cmd.name :: args'}"
  pure (runIdentity $ runEitherT $ parse cmd args')
