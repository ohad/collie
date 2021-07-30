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

%default total

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

public export
record Handlers (a : Type) (cmd : Field Command) where
  constructor MkHandlers
  here  : ParsedCommand Prelude.id Maybe (cmd .fst) (cmd .snd) -> a
  there : Checkable (Handlers a) cmd.snd.subcommands

||| Givent that we already have list syntax to build records, this gives us the
||| ability to use list syntax to build `Handlers`: the head will be the handler
||| for the toplevel command and the tail will go towards building the record of
||| handlers for the subcommands.
public export
(::) : (ParsedCommand Prelude.id Maybe (cmd .fst) (cmd .snd) -> a) ->
       Checkable (Handlers a) cmd.snd.subcommands ->
       Handlers a cmd
(::) = MkHandlers

infixr 4 ~~>

||| A nicer notation for handlers
public export
0 (~~>) : (Command arg) -> Type -> Type
(~~>) cmd a = Handlers a (_ ** cmd)

||| Handling a parsetree is pretty simple: use `there` together with `(!!)` to
||| select the appropriate subhandler while you're encountering  the `There`
||| constructor and finish up with `here`.
public export
handle : {0 cmd : Field Command} ->
         ParseTree Prelude.id Maybe cmd.snd -> Handlers a cmd -> a
handle (Here res)    h = h.here res
handle (There pos p) h = handle p $ content h.there.mkCheckable !! pos

||| Finally we can put the various pieces together to get a toplevel command
||| parsing the arguments and handling the resulting command using the
||| user-provided handlers
public export
(.handleWith) : {nm : String} -> (cmd : Command nm) -> (cmd ~~> IO a) -> IO a
cmd .handleWith h
  = do Right args <- cmd.parseArgs
         | _ => do putStrLn (cmd .usage)
                   exitFailure
       handle args h
