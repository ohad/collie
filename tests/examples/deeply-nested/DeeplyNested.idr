||| An example using the handlers-based approach

module DeeplyNested

import Collie
import Data.List.Quantifiers
import Data.List

%default total

Turns : Command [< "TOP"]
Turns = MkCommand
  { description = "A deeply nested example"
  , subcommands = turns $ turns []
  , modifiers = ["--help" ::= flag "Print usage"]
  , arguments = lotsOf filePath
  } where

  left : Fields (Command . ((p :< "left") :<)) -> Command (p :< "left")
  left cmds = MkCommand
    { description = "Took a left turn"
    , subcommands = cmds
    , modifiers = ["--help" ::= flag "Print usage"]
  , arguments   = none
    }

  right : Fields (Command . ((p :< "right") :<)) -> Command (p :< "right")
  right cmds = MkCommand
    { description = "Took a right turn"
    , subcommands = cmds
    , modifiers = ["--help" ::= flag "Print usage"]
    , arguments   = none
    }

  turns : ({0 str : _} -> Fields (Command . ((p :< str) :<))) ->
          Fields (Command . (p :<))
  turns cmds = [ "left"  ::= left cmds
               , "right" ::= right cmds
               ]

usageOrMsg : {nm : _} -> Command nm -> Bool -> String -> IO ()
usageOrMsg cmd b msg = putStrLn (ifThenElse b cmd.usage msg)

handle' : Turns ~:> IO ()
handle' "           " args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                           $ let files = fromMaybe [] args.arguments in
                             "Received the files: \{show files}"
handle' "right      " args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Took a right turn"
handle' "right left " args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Back to the start (rl)"
handle' "right right" args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Half turn, rightwise"
handle' "left       " args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Took a left turn"
handle' "left  left " args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Half turn, leftwise"
handle' "left  right" args = usageOrMsg (theParsedCommand args)
                                        (args.modifiers .project "--help")
                                        "Back to the start (lr)"


{-
handle' : Turns ~:> IO ()
handle' "           " args = let files = fromMaybe [] args.arguments in
                             putStrLn "Received the files: \{show files}"
handle' "right      " args = putStrLn "Took a right turn"
handle' "right left " args = putStrLn "Back to the start (rl)"
handle' "right right" args = putStrLn "Half turn, rightwise"
handle' "left       " args = putStrLn "Took a left turn"
handle' "left  left " args = putStrLn "Half turn, leftwise"
handle' "left  right" args = putStrLn "Back to the start (lr)"
-}

main : IO ()
main = do -- Turns .handleWith handle
          Turns .handleWith' handle'
