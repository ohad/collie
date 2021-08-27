||| An ordered record is a record whose field names have to appear in
||| a fixed order, but must otherwise be distinct.
module Data.Record

import public Data.List.Fresh
import public Data.List.Fresh.Quantifiers
import Data.Fin
import Data.DPair
import public Decidable.Decidable.Extra1
import public Decidable.Equality

%default total

public export
ArgList : Type
ArgList = FreshList String String.(##)

public export
Field : (String -> Type) -> Type
Field a = (nm : String ** a nm)

public export
Fields : (String -> Type) -> Type
Fields a = FreshList (Field a) ((##) `on` fst)

public export
record Record {0 A : String -> Type}
              (0 F : Field A -> Type)
              (0 Flds : Fields A) where
  constructor MkRecord
  content : All F Flds

namespace Record

  public export
  map : {flds : Fields a} -> ((x : Field a) -> f x -> g x) ->
    Record f flds -> Record g flds
  map f (MkRecord rec) = MkRecord (All.map f rec)

public export
IsField : (fldName : String) -> (flds : Fields a) -> Type
IsField fldName flds = Any (\ u => fldName === fst u) flds

public export
isYesBecause : (d : Dec p) -> p -> IsYes d
isYesBecause (Yes prf) p = ItIsYes
isYesBecause (No nprf) p = absurd (nprf p)

-- Todo: move to base
public export
soNotToEq : {b : Bool} -> So (not b) -> b = False
soNotToEq {b = False} Oh = Refl

public export
stringEq : {x, y : String} -> x === y -> (x == y) === True
stringEq eq = go (decEq x y `isYesBecause` eq) where

  go : IsYes (decEq x y) -> (x == y) === True
  go p with (x == y)
   go p | True = Refl

public export
IsFieldStale : nm `IsField` flds -> fst nmv === nm ->
               (0 fresh : nmv # flds) -> Void
IsFieldStale (Here Refl) eq fresh
  = absurd $ trans (sym $ stringEq eq) (soNotToEq $ fst $ soAnd fresh)
IsFieldStale (There pos) eq fresh
  = IsFieldStale pos eq (snd $ soAnd fresh)

public export
IsFieldIrrelevant : (p, q : nm `IsField` flds) -> p === q
IsFieldIrrelevant (Here Refl) (Here Refl) = Refl
IsFieldIrrelevant (Here Refl) (There {fresh} p)
  = void $ IsFieldStale p Refl fresh
IsFieldIrrelevant (There {fresh} p) (Here Refl)
  = void $ IsFieldStale p Refl fresh
IsFieldIrrelevant (There p) (There q)
  = cong There (IsFieldIrrelevant p q)

public export
isField : (fldName : String) -> (flds : Fields a) ->
  Dec (fldName `IsField` flds)
isField fldName flds = any (\u => decEq fldName (fst u)) flds

public export
field : {flds : Fields a} -> (pos : Any p flds) -> Field a
field pos = lookup pos

public export
(.project) : {flds : Fields a} -> (rec : Record f flds) -> (name : String) ->
  {auto pos : IsYes $ name `isField` flds} -> f (field $ toWitness pos)
rec.project name = rec.content !! _

public export
tabulate :
  (args : ArgList) ->
  (f : (arg : String) -> Any (arg ===) args -> a arg) ->
  Fields a

public export
0 tabulateFreshness : {0 a : String -> Type} -> (args : ArgList) ->
  (f : (arg : String) -> Any (arg ===) args -> a arg) ->
  {0 y : String} -> {0 u : a y} ->
  (y # args) -> (y ** u) # tabulate args f

tabulate [] f = []
tabulate ((x :: xs) {fresh}) f
  = ((x ** f x (Here Refl)) :: tabulate xs (\u, pos => f u $ There pos))
    {fresh = tabulateFreshness xs _ fresh}

tabulateFreshness    []     f fresh = Oh
tabulateFreshness (x :: xs) f fresh
  = let (y_fresh_x, y_fresh_xs) = soAnd fresh in
    andSo (y_fresh_x, tabulateFreshness xs _ y_fresh_xs)

public export
map : (f : (nm : String) -> a nm -> b nm) -> Fields a -> Fields b
map f = Data.List.Fresh.map
        (\ (nm ** a) => (nm ** f nm a))
        (\(_**_), (_**_) => id)

public export
foldl : (f : b -> a -> b) -> b -> Record (const a) flds -> b
foldl f x = foldl f x . content

public export
TypeFields : {flds : Fields a} ->
             (rec : Record (const Type) flds ) -> Fields (const Type)
TypeFields rec = Fresh.map (\ ((nm ** _) ** ty) => (nm ** ty))
    (\((_**_) ** _),((_**_) ** _) => id)
    (rec.content.toFreshList)

public export
PartialRecord : (f : Field a -> Type) -> Fields a -> Type
PartialRecord f flds = Record (Maybe . f) flds

public export
traverse : {flds : Fields a} ->
           Applicative m =>
           ((x : Field a) -> f x -> m (g x)) ->
           Record f flds  -> m (Record g flds)
traverse f rec = MkRecord <$> (Quantifiers.traverse f rec.content)

public export
sequence : Applicative g =>
           Record (g . f) flds  -> g (Record f flds)
sequence rec = MkRecord <$> (Quantifiers.sequence rec.content)
