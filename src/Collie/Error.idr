module Collie.Error

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
Error : Type -> Type
Error = Either ErrorMsg

export
throwE : ErrorMsg -> Error a
throwE = Left

export
Show ErrorMsg where

  show err = "*** Error: " ++ case err of
    CouldNotParse str => "Could not parse argument: \{str}"
    MissingOption str => "Missing required modifier: \{str}"
    MissingArgument   => "Missing required argument"
    OptionSetTwice nm => "Option \{nm} set twice"
    TooManyArguments  => "Too many arguments, only one expected"
    MissingOptArg nm  => "Missing argument for option \{nm}"
