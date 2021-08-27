module Collie.Error

import Data.List1
import Data.String
import System

%default total

public export
data ErrorMsg : Type where
  CouldNotParse    : String -> ErrorMsg
  MissingOption    : String -> ErrorMsg
  MissingArgument  : ErrorMsg
  OptionSetTwice   : String -> ErrorMsg
  TooManyArguments : ErrorMsg
  MissingOptArg    : String -> ErrorMsg

-- TODO: use an accumulating error monad instead
public export
data Error : Type -> Type where
  Fail : List1 ErrorMsg -> Error a
  Pure : a -> Error a

export
throwE : ErrorMsg -> Error a
throwE err = Fail (err ::: [])

export
fromEither : Either ErrorMsg a -> Error a
fromEither (Left err) = throwE err
fromEither (Right a)  = Pure a

export
Functor Error where
  map f (Fail err) = Fail err
  map f (Pure a) = Pure (f a)

export
Applicative Error where
  pure = Pure
  Pure f   <*> Pure x   = Pure (f x)
  Fail es1 <*> Fail es2 = Fail (es1 ++ es2)
  Fail es1 <*> Pure x   = Fail es1
  Pure f   <*> Fail es2 = Fail es2

export
(>>=) : Error a -> (a -> Error b) -> Error b
Fail es >>= _ = Fail es
Pure x  >>= f = f x

export
Show ErrorMsg where

  show (CouldNotParse str) = "Could not parse argument: \{str}"
  show (MissingOption str) = "Missing required modifier: \{str}"
  show MissingArgument     = "Missing required argument"
  show (OptionSetTwice nm) = "Option \{nm} set twice"
  show TooManyArguments    = "Too many arguments, only one expected"
  show (MissingOptArg nm)  = "Missing argument for option \{nm}"


export
Show a => Show (Error a) where
  show (Pure a) = show a
  show (Fail (err ::: [])) = "*** Error: " ++ show err
  show (Fail errs) = unlines
                   $ "*** Errors:"
                   :: map (("  " ++) . show) (forget errs)

export
exitWith : List1 ErrorMsg -> IO a
exitWith errs
  = do putStr (show $ the (Error ()) $ Fail errs)
       exitFailure
