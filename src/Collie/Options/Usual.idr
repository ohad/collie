module Collie.Options.Usual

import Collie.Options.Domain
import Data.Magma

public export
none : Arguments
none = MkArguments (Some Void) $ const $ throwE $ "Argument provided when none expected"

public export
lotsOf : Arguments -> Arguments
lotsOf args@(MkArguments {}) = MkArguments
  (ALot (List.rawMagma (Carrier args.domain)))
  (((:: []) <$>) . args.parser)

public export
Regex : Type
Regex = String

public export
regex : Arguments
regex = MkArguments (Some Regex) pure

public export
FilePath : Type
FilePath = String

public export
filePath : Arguments
filePath = MkArguments (Some FilePath) pure

public export
Regexp : Type
Regexp = String

public export
regexp : Arguments
regexp = MkArguments (Some Regexp) pure

public export
Url : Type
Url = String

public export
url : Arguments
url = MkArguments (Some Url) pure

public export
nat : Arguments
-- TODO: Parse Nat properly
nat = MkArguments (Some Nat) (pure . cast)

public export
integer : Arguments
-- TODO: Parse Integer properly
integer = MkArguments (Some Integer) (pure . cast)
