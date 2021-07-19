module Record

import Data.Record.Ordered
import Data.Record.Ordered.SmartConstructors

rec : BasicRecord Prelude.id ?
rec = [ "first"  ::= 1
      , "second" ::= "string"
      , "third"  ::= 'a'
      , "fourth" ::= MkBasicRecord {f = List} [ "unwrap" ::= [1..10] ]
      ]

-- TODO: add Show instance for records whose content can be shown
