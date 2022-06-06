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
import public Data.Record
import public Data.Record.SmartConstructors

import public Data.DPair
import public Data.Magma

import public Data.Either
import public Data.String

import public System

%default total

public export
(.parseArgs) : {nm : _} -> (cmd : Command nm) -> HasIO io =>
  io (String `Either` ParseTreeT Maybe Maybe cmd)
cmd.parseArgs = do
  args <- getArgs
  let args' =
        case args of
          [] => []
          _ :: xs => xs
  -- putStrLn "parsing arguments: \{show $ cmd.name :: args'}"
  let Pure res = parse cmd args'
       | err => pure $ Left (show (() <$ err))
  pure $ Right res


public export
record Handlers (a : Type) {p : _} (cmd : Field (CommandAt p)) where
  constructor MkHandlers
  here  : ParsedCommand ? (cmd.snd) -> a
  there : Checkable (Handlers a) cmd.snd.subcommands

||| Givent that we already have list syntax to build records, this gives us the
||| ability to use list syntax to build `Handlers`: the head will be the handler
||| for the toplevel command and the tail will go towards building the record of
||| handlers for the subcommands.
public export
(::) : (ParsedCommand ? (cmd .snd) -> a) ->
       Checkable (Handlers a) cmd.snd.subcommands ->
       Handlers a cmd
(::) = MkHandlers

infixr 4 ~~>

||| A nicer notation for handlers
public export
0 (~~>) : CommandAt p nm -> Type -> Type
(~~>) cmd a = Handlers a (_ ** cmd)

||| Handling a parsetree is pretty simple: use `there` together with `(!!)` to
||| select the appropriate subhandler while you're encountering  the `There`
||| constructor and finish up with `here`.
public export
handle : {0 cmd : Field (CommandAt p)} ->
         ParseTree cmd.snd -> Handlers a cmd -> a
handle (Here res)    h = h.here res
handle (There pos p) h = handle p $ content h.there.mkCheckable !! pos

||| Finally we can put the various pieces together to get a toplevel command
||| parsing the arguments and handling the resulting command using the
||| user-provided handlers
public export
(.handleWith) : {p, nm : _} -> (cmd : CommandAt p nm) -> (cmd ~~> IO a) -> IO a
cmd .handleWith h
  = do Right args <- cmd.parseArgs
         | _ => do putStrLn (cmd .usage)
                   exitFailure
       let Pure args = ParsedTree.finalising args
         | Fail err => exitWith err
       handle args h

namespace Focus

  public export
  data Focus : {- (foc : List String) -> -} Command arg -> Type where
    Nil  : Focus {-[]-} cmd
    (::) : {0 arg : _} -> {0 sub : String} -> {- {0 foc : _} -> -}
           {0 cmd : Command arg} ->
           (pos : sub `IsField` cmd.subcommands) ->
           Focus {-        foc              -} (snd $ field pos) ->
           Focus {-(fst (field pos) :: foc) -}cmd

  public export
  toMaybe : Dec p -> Maybe p
  toMaybe (Yes prf) = Just prf
  toMaybe (No _) = Nothing

  namespace Verb

    public export
    focus : (subs : List String) -> (c : Command arg) ->
            Maybe (Focus {- subs -} c)
    focus []            cmd = pure []
    focus (sub :: subs) cmd
      = do pos <- toMaybe (sub `isField` cmd.subcommands)
           tl <- focus subs (snd $ field pos)
           pure (pos :: tl)

  public export
  fromString : (str : String) -> {c : Command arg} ->
               Either String (Focus c)
  fromString str = maybeToEither ("Invalid command: " ++ str)
                 $ focus (assert_total $ words str) c

  namespace Noun

    public export
    focus : {arg : _} -> {cmd : Command arg} ->
            Focus cmd -> (foc : _ ** Command foc)
    focus []         = (_ ** cmd)
    focus (_ :: foc) = focus foc

data Error : String -> Type where

infixr 4 ~:>

public export
0 (~:>) : (Command arg) -> Type -> Type
(~:>) cmd a = (mfoc : Either String (Focus cmd)) ->
              either Error (\ foc => ParsedCommand ? (snd $ focus foc)) mfoc ->
              either Error (const a) mfoc

||| Handling a parsetree is pretty simple: use `there` together with `(!!)` to
||| select the appropriate subhandler while you're encountering  the `There`
||| constructor and finish up with `here`.
public export
handle' : {0 nm : _} -> {0 cmd : Command nm} ->
         ParseTree cmd -> (cmd ~:> a) -> a
handle' (Here res)    h = h (Right []) res
handle' (There pos p) h = handle' p $ \case
  Left _    => id
  Right loc => h (Right (pos :: loc))

public export
(.handleWith') : {nm : _} -> (cmd : Command nm) -> (cmd ~:> IO a) -> IO a
cmd .handleWith' h
  = do Right args <- cmd.parseArgs
         | _ => do putStrLn (cmd .usage)
                   exitFailure
       let Pure args = ParsedTree.finalising args
         | Fail err => exitWith err
       handle' args h
