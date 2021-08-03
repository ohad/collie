module Record

import Data.List.Fresh
import Data.Record.Ordered
import Data.Record.Ordered.SmartConstructors

rec : BasicRecord Prelude.id ?
rec = mkInferrable
    [ "first"  ::= 1
    , "second" ::= "string"
    , "third"  ::= 'a'
    , "fourth" ::= mkBasicRecord {f = List}
                   (mkInferrable [ "unwrap" ::= [1..10] ])
    ]

Types : Fields (const Type)
Types = [("nat" ** Nat), ("int" ** Int)]

Values : BasicRecord Prelude.id Types
Values = mkCheckable
  [ "int" ::= 3
  , "nat" ::= 2
  ]

-- TODO: add Show instance for records whose content can be shown
