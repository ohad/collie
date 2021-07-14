||| Collie: Command line interface for Idris2 applications
|||
||| Based on Guillaume Allais's agdARGS library:
|||
||| https://github.com/gallais/agdargs/
module Collie

import Collie.Options.Domain

public export
record Option where
  constructor MkOption
  name        : String
  description : String
  flag        : String
  optional    : Bool
  domain      : Domain
  parser      : Parser domain
