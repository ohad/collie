||| An ordered record is a record whose field names have to appear in
||| a fixed order, but must otherwise be distinct.
module Data.Record.Ordered

import public Data.List.Fresh
import public Data.List.Fresh.Quantifiers
import Data.Fin
import public Decidable.Decidable.Extra
import public Decidable.Equality

public export
ArgList : Type
ArgList = FreshList String String.(#)

public export
Fields : Type -> Type
Fields a = FreshList (String, a) ((#) `on` fst)

public export
record Record {0 A : Type} (0 F : A -> Type) (0 Flds : Fields A) where
  constructor MkRecord
  content : All (F . Builtin.snd) Flds

namespace Record

  public export
  map : {flds : Fields a} -> (String -> (x : a) -> f x -> g x) ->
    Record f flds -> Record g flds
  map f (MkRecord rec) = MkRecord (All.map (\ (str, x) => f str x) rec)

public export
IsField : (fldName : String) -> (flds : Fields a) -> Type
IsField fldName flds = Any (\ u => fldName === fst u) flds

public export
isField : (fldName : String) -> (flds : Fields a) ->
  Dec (fldName `IsField` flds)
isField fldName flds = any (\u => decEq fldName (fst u)) flds

public export
field : {flds : Fields a} -> (pos : Any p flds) -> a
field pos = snd (lookup pos)

public export
(.project) : {flds : Fields a} -> (rec : Record f flds) -> (name : String) ->
  {auto pos : IsYes $ name `isField` flds} -> f (field $ toWitness pos)
rec.project name = rec.content !! _

public export
tabulate : (args : ArgList) -> (f : (arg : String) -> Any (arg ===) args -> a) -> Fields a

public export
tabulateFreshness : (args : ArgList) -> (f : (arg : String) -> Any (arg ===) args -> a) ->
  (y # args) -> (y, u) # tabulate args f

tabulate [] f = []
tabulate ((x :: xs) {fresh}) f = ((x, f x (Here Refl)) :: tabulate xs (\u, pos => f u $ There pos))
  {fresh = tabulateFreshness xs _ fresh}

tabulateFreshness    []     f x = ()
tabulateFreshness (x :: xs) f (y_fresh_x, y_fresh_xs)
  = (y_fresh_x, tabulateFreshness xs _ y_fresh_xs)

namespace Fields

  public export
  map : (f : a -> b) -> Fields a -> Fields b
  map f = Data.List.Fresh.map (map f) (\(_,_), (_,_) => id)

public export
foldl : (f : b -> a -> b) -> b -> Record (const a) flds -> b
foldl f x = foldl f x . content

public export
TypeFields : {flds : Fields a} -> (rec : Record (const Type) flds ) -> Fields Type
TypeFields rec = Fresh.map (\x => (Builtin.fst x.fst, x.snd))
    (\((_,_) ** _),((_,_) ** _) => id)
    (rec.content.toFreshList)

public export
PartialRecord : (f : a -> Type) -> Fields a -> Type
PartialRecord f flds = Record (Maybe . f) flds

public export
sequence : Applicative g => Record (g . f) flds  -> g (Record f flds)
sequence rec = MkRecord <$> (Quantifiers.sequence rec.content)
