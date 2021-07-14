module Collie.Options.Predefined

import Collie.Options

flag : Option
flag
  = MkOption
  { name = "defaule name"
  , description = "default desceription"
  , flag = ""
  , optional = True
  , domain = Some Unit
  , parser = \_ => pure ()
  }
