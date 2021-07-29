module DeeplyNested

import Collie

%default total

Turns : Command "TOP"
Turns = MkCommand
  { description = "A deeply nested example"
  , subcommands = turns [] -- $ turns []
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

handle : Turns -=-> IO ()
handle [] = ?a
handle ["left"] = ?atnbzg
-- handle ["right"] = ?atnbza
-- handle ["left", "left"] = ?atnbegfha
-- handle ["left", "right"] = ?atnba
-- handle ["right", "right"] = ?atnbehth
-- handle ["right", "left"] = ?atnbehre
handle {covers = %search} _ impossible
