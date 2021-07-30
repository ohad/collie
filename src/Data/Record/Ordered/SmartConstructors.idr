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
record Entry
  (a    : String -> Type)
  (f    : Field a -> Type)
  (flds : Fields a) where
  constructor (::=)
  name  : String
  {auto 0 pos : IsYes (name `isField` flds)}
  value : f (field (toWitness pos))

public export
(::) : {flds : Fields a} ->
       (entry : Entry a f flds) ->
       Record f (remove (toWitness entry.pos)) ->
       Record f flds
((name ::= value) {pos}) :: rec
  = MkRecord $ insertLookedup (toWitness pos) value rec.content

||| A record where the notion of type for its fields is `Type` itself
public export
BasicRecord : (f : Type -> Type) -> Fields (const Type) -> Type
BasicRecord f flds = Record (\ x => f (snd x)) flds

||| This acts as a type annotation ensuring the list passed as an
||| argument is a basic record.
public export
MkBasicRecord : BasicRecord f flds -> BasicRecord f flds
MkBasicRecord rec = rec
