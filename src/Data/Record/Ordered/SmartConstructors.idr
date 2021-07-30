||| Selectively ported from agdARGS's Data.Recrod.SmartConstructors
|||
||| Please port more if you want!
module Data.Record.Ordered.SmartConstructors

import Data.Record.Ordered

%default total

namespace Check

  public export
  record Checkable
    {a : String -> Type}
    (f : Field a -> Type)
    (flds : Fields a) where
    constructor MkCheckable
    mkCheckable : Record f flds

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
  Nil : Checkable f []
  Nil = MkCheckable $ MkRecord []

  public export
  (::) : {flds : Fields a} ->
         (entry : Entry a f flds) ->
         Checkable f (remove (toWitness entry.pos)) ->
         Checkable f flds
  ((name ::= value) {pos}) :: rec
    = MkCheckable
    $ MkRecord
    $ insertLookedup (toWitness pos) value rec.mkCheckable.content


namespace Infer

  public export
  record Inferrable
    {a : String -> Type}
    (f : Field a -> Type)
    (flds : Fields a) where
    constructor MkInferrable
    mkInferrable : Record f flds

  infix 1 ::=
  public export
  record Entry (a : String -> Type) (f : Field a -> Type) where
    constructor (::=)
    name  : String
    {type : a name}
    value : f (name ** type)

  public export
  Nil : Inferrable f []
  Nil = MkInferrable $ MkRecord []

  public export
  (::) : {flds : Fields a} ->
         (entry : Entry a f) ->
         (rec : Inferrable f flds) ->
    {auto fresh : IsYes (decideFreshness (entry.name ** entry.type)
                        (\y => (entry.name #? (fst y))) flds)} ->
    Inferrable f (((entry.name ** entry.type) :: flds)
                 {fresh = toWitness fresh})
  ((name ::= value) :: rec)
    = MkInferrable
    $ MkRecord
    $ (value :: rec.mkInferrable.content) {fresh = toWitness fresh}

||| A record where the notion of type for its fields is `Type` itself
public export
BasicRecord : (f : Type -> Type) -> Fields (const Type) -> Type
BasicRecord f flds = Record (\ x => f (snd x)) flds

||| This acts as a type annotation ensuring the list passed as an
||| argument is a basic record.
public export
mkBasicRecord : BasicRecord f flds -> BasicRecord f flds
mkBasicRecord rec = rec
