||| Selectively ported from agdARGS's Data.Recrod.SmartConstructors
|||
||| Please port more if you want!
module Data.Record.Ordered.SmartConstructors

import Data.Record.Ordered

%default total

public export
Nil : Record f []
Nil = MkRecord []

infix 1 ::=
public export
record Entry (a : String -> Type) (f : Field a -> Type) where
  constructor (::=)
  name  : String
  {type : a name}
  value : f (name ** type)

public export
(::) : {flds : Fields a} ->
       (entry : Entry a f) ->
       (rec : Record f flds) ->
  {auto fresh : IsYes (decideFreshness (entry.name ** entry.type)
                      (\y => (entry.name #? (fst y))) flds)} ->
  Record f (((entry.name ** entry.type) :: flds)
           {fresh = toWitness fresh})
((name ::= value) :: rec)
  = MkRecord ((value :: rec.content) {fresh = toWitness fresh})

||| A record where the notion of type for its fields is `Type` itself
public export
BasicRecord : (f : Type -> Type) -> Fields (const Type) -> Type
BasicRecord f flds = Record (\ x => f (snd x)) flds

||| This acts as a type annotation ensuring the list passed as an
||| argument is a basic record.
public export
MkBasicRecord : BasicRecord f flds -> BasicRecord f flds
MkBasicRecord rec = rec

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
