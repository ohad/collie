module Main

import Test.Golden

%default covering

tests : TestPool
tests = MkTestPool "Examples using Collie" [] Nothing
  [ "idealised-git"
  ]

main : IO ()
main = runner [ record { testCases $= map ("examples/" ++) } tests ]
