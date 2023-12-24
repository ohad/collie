module Main

import Test.Golden

%default covering

performance : TestPool
performance = MkTestPool "Performance regression tests" [] Nothing
  [ "issue16"
  ]

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
  , withPath "performance" performance
  ]

 where
   withPath : String -> TestPool -> TestPool
   withPath path pool = { testCases $= map (path ++ "/" ++) } pool
