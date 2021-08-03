||| An example using the handlers-based approach

module DeeplyNested

import Collie
import Data.List.Quantifiers

%default total

Turns : Command "TOP"
Turns = MkCommand
  { description = "A deeply nested example"
  , subcommands = turns $ turns []
  , modifiers = []
  , arguments = lotsOf filePath
  } where

  left : Fields Command -> Command "left"
  left cmds = MkCommand
    { description = "Took a left turn"
    , subcommands = cmds
    , modifiers   = []
    , arguments   = none
    }

  right : Fields Command -> Command "right"
  right cmds = MkCommand
    { description = "Took a right turn"
    , subcommands = cmds
    , modifiers   = []
    , arguments   = none
    }

  turns : Fields Command -> Fields Command
  turns cmds = [ "left"  ::= left cmds
               , "right" ::= right cmds
               ]

handle : Turns ~~> IO ()
handle
  = [ (\ args => let files = fromMaybe Prelude.Nil args.arguments in
                 putStrLn "Received the files: \{show files}")
    , "right" ::= [ const $ putStrLn "Took a right turn"
                  , "left"  ::= [ const $ putStrLn "Back to the start (rl)" ]
                  , "right" ::= [ const $ putStrLn "Half turn, rightwise" ]
                  ]
    , "left"  ::= [ const $ putStrLn "Took a left turn"
                  , "right" ::= [ const $ putStrLn "Back to the start (lr)" ]
                  , "left"  ::= [ const $ putStrLn "Half turn, leftwise" ]
                  ]
    ]

main : IO ()
main = Turns .handleWith handle
