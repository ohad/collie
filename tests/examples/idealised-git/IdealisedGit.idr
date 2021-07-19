module IdealisedGit

import Collie

git : Command "idealised-git"
git = MkCommand
  { description = """
                  A distributed revision control system with an emphasis on speed, \
                  data integrity, and support for distributed, non-linear workflows
                  """
  , subcommands =
     [ "--help" ::= basic "Print this help text." none
     , "add"    ::= basic "Add file contents to the index" (lotsOf filePath)
     , "clone"  ::= basic "Clone a repository into a new directory" url
     , "push"   ::= gitPush
     ]
  , modifiers = []
  , arguments = lotsOf filePath
  }
  where
    gitPush : Command "push"
    gitPush = MkCommand
      { name = "push"
      , description = "Update remote refs along with associated objects"
      , subcommands = []
      , modifiers = [
            "--force" ::= (flag $ """
                                  Usually, the command refuses to update a remote ref that \
                                  is not an ancestor of the local ref used to overwrite it. This \
                                  flag disables the check. This can cause the remote repository \
                                  to lose commits; use it with care.
                                  """)
          ]
      , arguments = none
      }


{nm : String} -> {cmd : Command nm} -> Show (ParseTree cmd) where
  show (Here x) = "\{nm} <<args>>"
  show (There pos parsedSub) = "\{nm} \{show parsedSub}"


main : IO Builtin.Unit
main = do
  Right cmdParse <- git.withArgs
  | Left err => putStrLn "Error: \{err}"
  case fst (lookup cmdParse) of
    "--help" => putStrLn "Usage:\n\{git.usage}"
    _ => putStrLn "Parsed as: \{show cmdParse}"
  putStrLn ""
