||| Selectively ported from agdARGS's Data.Recrod.SmartConstructors
|||
||| Please port more if you want!
module Data.Record.Ordered.SmartConstructors

import Data.Record.Ordered


public export
Nil : Record [] flds
Nil = MkRecord ()

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
(::=) : (recpos : (Record args flds, arg `Elem` args)) -> flds.lookup (snd recpos) -> Record args flds
(rec, pos) ::= v = MkRecord $ UPDATE rec.content pos v
