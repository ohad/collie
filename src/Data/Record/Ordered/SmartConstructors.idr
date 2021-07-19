||| Selectively ported from agdARGS's Data.Recrod.SmartConstructors
|||
||| Please port more if you want!
module Data.Record.Ordered.SmartConstructors

import Data.Record.Ordered


public export
Nil : Record f []
Nil = MkRecord []

public export
(::) : {x : a} -> {flds : Fields a} ->
  (namearg : (String, f x)) ->
   (rec : Record f flds) ->
  {auto 0 fresh : IsYes (decideFreshness (fst namearg, x) (\y => (fst namearg #? (fst y))) flds)} ->
  Record f (((fst namearg, x) :: flds) {fresh = toWitness fresh})
(name, arg) :: rec = MkRecord ((arg :: rec.content) {fresh = toWitness fresh})

{-
infixr 5 ::=

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
