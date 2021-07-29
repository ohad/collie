module Main

import Test.Golden

%default covering

datatypes : TestPool
datatypes = MkTestPool "Datatypes defined in Collie" [] Nothing
  [ "record"
  ]

tests : TestPool
tests = MkTestPool "Examples using Collie" [] Nothing
  [ "idealised-git"
  , "deeply-nested"
  ]

main : IO ()
main = runner
  [ withPath "examples" tests
  , withPath "data" datatypes
  ]

 where
   withPath : String -> TestPool -> TestPool
   withPath path pool = record { testCases $= map (path ++ "/" ++) } pool
