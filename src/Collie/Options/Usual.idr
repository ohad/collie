module Collie.Options.Usual

import Collie.Options.Domain
import Data.Magma

public export
Arguments : Type
Arguments = (d : Domain ** Parser d)

public export
none : Arguments
none = (Some Void ** const $ throwE $ "Argument provided when none expected")

public export
lotsOf : Arguments -> Arguments
lotsOf (d ** p) = (ALot (List.rawMagma (Carrier d))  ** ((:: []) <$>) . p)

public export
Regex : Type
Regex = String

public export
regex : Arguments
regex = (Some Regex ** pure)

public export
FilePath : Type
FilePath = String

public export
filePath : Arguments
filePath = (Some FilePath ** pure)

public export
Regexp : Type
Regexp = String

public export
regexp : Arguments
regexp = (Some Regexp ** pure)

public export
Url : Type
Url = String

public export
url : Arguments
url = (Some Url ** pure)

public export
nat : Arguments
-- TODO: Parse Nat properly
nat = (Some Nat ** pure . cast)

public export
integer : Arguments
-- TODO: Parse Integer properly
integer = (Some Integer ** pure . cast)
