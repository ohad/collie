module Collie.Options.Usual

import Collie.Options.Domain
import Data.Magma
import Data.String

%default total

public export
none : Arguments
none = MkArguments
     False
     (Some Void)
     (const $ Left "Argument provided when none expected")

public export
lotsOf : Arguments -> Arguments
lotsOf args@(MkArguments {}) = MkArguments
  False
  (ALot (List.rawMagma (Carrier args.domain)))
  (((:: []) <$>) . args.rawParser)

public export
Regex : Type
Regex = String

public export
regex : Arguments
regex = MkArguments False (Some Regex) pure

public export
FilePath : Type
FilePath = String

public export
filePath : Arguments
filePath = MkArguments False (Some FilePath) pure

public export
Regexp : Type
Regexp = String

public export
regexp : Arguments
regexp = MkArguments False (Some Regexp) pure

public export
Url : Type
Url = String

public export
url : Arguments
url = MkArguments False (Some Url) pure

public export
nat : Arguments
-- TODO: Parse naturals properly
nat = MkArguments False (Some Nat) $ \ str =>
  case parsePositive str of
    Nothing => Left $ "Expect a natural number, got: " ++ str
    Just n => pure n

public export
integer : Arguments
integer = MkArguments False (Some Integer) $ \ str =>
  case parseInteger str of
    Nothing => Left $ "Expect an integer, got: " ++ str
    Just n => pure n
