module Issue16

import Collie

idv : Command "idv"
idv = MkCommand
  { description = ""
  , subcommands =
     [ "--help"  ::= basic "Print this help text." none
     , "list"    ::= basic "List all installed and available Idris 2 versions." none
     , "install" ::= installCommand
     ]
  , modifiers = []
  , arguments = none
  }
  where
    installCommand : Command "install"
    installCommand = MkCommand
      { name = "install"
      , description = ""
      , subcommands = []
      , modifiers = ["--api" ::= flag ""]
      , arguments = MkArguments False (Some String) Right
      }

    selectCommand : Command "select"
    selectCommand = MkCommand
      { name = "select"
      , description = ""
      , subcommands =
        [ "system" ::= basic "" none ]
      , modifiers = []
      , arguments = MkArguments False (Some String) Right
      }

handleCommand' : Issue16.idv ~~> IO ()
handleCommand' =
  [ const (putStrLn "Expected a subcommand.")
  , "--help"  ::= [ const $ putStrLn idv.usage ]
  , "list"    ::= [ const $ putStrLn "list" ]
  , "install" ::= [ (\args => case args.arguments of
                                   Nothing      => putStrLn "fail"
                                   Just version => if args.modifiers.project "--api"
                                                        then putStrLn "install plus API"
                                                        else putStrLn "just install"
                    ) ]
  ]
