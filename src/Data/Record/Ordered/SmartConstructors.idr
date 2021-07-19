||| Selectively ported from agdARGS's Data.Recrod.SmartConstructors
|||
||| Please port more if you want!
module Data.Record.Ordered.SmartConstructors

import Data.Record.Ordered

public export
Nil : Record f []
Nil = MkRecord []

infix 1 ::=
record Entry (a : String -> Type) (f : Field a -> Type) where
  constructor (::=)
  name  : String
  {type : (str : String) -> a str}
  value : f (name ** type name)

public export
(::) : {flds : Fields a} ->
       (entry : Entry a f) ->
       (rec : Record f flds) ->
  {auto fresh : IsYes (decideFreshness (entry.name ** entry.type entry.name)
                      (\y => (entry.name #? (fst y))) flds)} ->
  Record f (((entry.name ** entry.type entry.name) :: flds)
           {fresh = toWitness fresh})
((name ::= value) :: rec)
  = MkRecord ((value :: rec.content) {fresh = toWitness fresh})

{-
public export
(~>) : (Record args flds) -> (0 arg : String) -> {auto pos : arg `Elem` args} ->
  (Record args flds, arg `Elem` args)
(~>) rec arg {pos} = (rec, pos)

public export
UPDATE : RECORD args flds -> (pos : arg `Elem` args) -> flds.LOOKUP pos -> RECORD args flds
UPDATE (_, rec)  Here       v = (v, rec)
UPDATE (w, rec) (There pos) v = (w, UPDATE rec pos v)

public export
(::=) : (recpos : (Record args flds, arg `Elem` args)) ->
  flds.lookup arg {pos = snd recpos} -> Record args flds
(rec, pos) ::= v = MkRecord $ UPDATE rec.content pos v
-}
