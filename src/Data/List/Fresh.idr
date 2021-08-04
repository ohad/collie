||| Fresh lists, a variant of Catarina Coquand's contexts in "A
||| Formalised Proof of the Soundness and Completeness of a Simply
||| Typed Lambda-Calculus with Explicit Substitutions"
|||
||| Based directly on Agda's fresh lists:
||| http://agda.github.io/agda-stdlib/Data.List.Fresh.html
module Data.List.Fresh

import public Control.Relation
import public Syntax.WithProof

infix 4 #, #?

public export
data FreshList : (a : Type) -> (neq : Rel a) -> Type

public export
(#) : {neq : Rel a} -> (x : a) -> (xs : FreshList a neq) -> Type

public export
data FreshList : (a : Type) -> (neq : Rel a) -> Type where
  Nil  : FreshList a neq
  (::) : (x : a) -> (xs : FreshList a neq) ->
         {auto 0 fresh : x # xs} ->
         FreshList a neq

%name FreshList xs, ys, zs

x #    []     = Unit
x # (y :: xs) = (x `neq` y, x # xs)

namespace FreshList1

  public export
  data FreshList1 : (a : Type) -> (neq : Rel a) -> Type where
    (::) : (x : a) -> (xs : FreshList a neq) ->
           {auto 0 fresh : x # xs} ->
           FreshList1 a neq

parameters
  {0 A : Type} {0 Aneq : Rel A}
  {0 B : Type} {0 Bneq : Rel B}
  (F : A -> B)
  (Injectivity : (x,y : A) -> x `Aneq` y -> F x `Bneq` F y)

  public export
  map : FreshList A Aneq -> FreshList B Bneq

  public export
  mapFreshness : {x : A} -> (ys : FreshList A Aneq) -> (x # ys) -> F x # map ys

  map     []              = []
  map ((x :: xs) {fresh}) = (F x :: map xs) {fresh = mapFreshness xs fresh}

  mapFreshness    []     _
    = ()
  mapFreshness (y :: ys) (x_fresh_y, x_fresh_ys)
    = (Injectivity _ _ x_fresh_y, mapFreshness ys x_fresh_ys)

namespace View
  public export
  data Empty : FreshList a neq -> Type where
    Nil : Empty Nil

  public export
  data NonEmpty : FreshList a neq -> Type where
    IsNonEmpty : NonEmpty ((x :: xs) {fresh})

public export
length : FreshList a neq -> Nat
length [] = 0
length (x :: xs) = 1 + length xs

public export
fromMaybe : Maybe a -> FreshList a neq
fromMaybe Nothing  = []
fromMaybe (Just x) = [x]

-- I don't include replicate since freshness ought not to be
-- reflexive, but feel free to add it if you need it

public export
uncons : FreshList a neq -> Maybe (a , FreshList a neq)
uncons    []     = Nothing
uncons (x :: xs) = Just (x, xs)

public export
toFreshList1 : FreshList a neq -> Maybe (FreshList1 a neq)
toFreshList1    []     = Nothing
toFreshList1 (x :: xs) = Just (x :: xs)

public export
head : (xs : FreshList a neq) -> (isNonEmpty : NonEmpty xs) => a
head (x :: xs) {isNonEmpty = IsNonEmpty} = x

public export
tail : (xs : FreshList a neq) -> (isNonEmpty : NonEmpty xs) => FreshList a neq
tail (x :: xs) {isNonEmpty = IsNonEmpty} = xs

public export
0 (.freshness) : (xs : FreshList a neq) -> (isNonEmpty : NonEmpty xs) => head xs # tail xs
(((x :: xs) {fresh}).freshness) {isNonEmpty = IsNonEmpty} = fresh

-- Freshness lemmata
parameters (0 x : a) (ys : FreshList a neq) {auto isNonEmpty : NonEmpty ys}
  public export
  headFreshness : x # ys -> x `neq` (head ys)

  public export
  tailFreshness : x # ys -> x # (tail ys)

headFreshness x (y :: ys) {isNonEmpty = IsNonEmpty} freshness = fst freshness
tailFreshness x (y :: ys) {isNonEmpty = IsNonEmpty} freshness = snd freshness

public export
take : Nat -> FreshList a neq -> FreshList a neq
public export
takeFreshness : (n : Nat) -> (xs : FreshList a neq) -> y # xs -> y # take n xs

take 0     xs                  = []
take (S n)     []              = []
take (S n) ((x :: xs) {fresh}) = (x :: take n xs) {fresh = takeFreshness n xs fresh}

takeFreshness  0          xs  fresh                 = ()
takeFreshness (S n)    []     fresh                 = ()
takeFreshness (S n) (x :: xs) (y_neq_x, y_fresh_xs) = (y_neq_x, takeFreshness n xs y_fresh_xs)

public export
drop : Nat -> FreshList a neq -> FreshList a neq
drop 0           xs  = xs
drop (S n)    []     = []
drop (S n) (x :: xs) = drop n xs

-- The Agda lib has more general takeWhile, dropWhile, filter
-- involving decidable predicts, but we follow the Idris stdlib and
-- use the special case for Bool

public export
takeWhile : (pred : a -> Bool) -> FreshList a neq -> FreshList a neq
public export
takeWhileFreshness : (pred : a -> Bool) -> (xs : FreshList a neq) ->
  y # xs -> y # takeWhile pred xs

takeWhile pred     []              = []
takeWhile pred ((x :: xs) {fresh}) = case pred x of
  True  => (x :: takeWhile pred xs) {fresh = takeWhileFreshness pred xs fresh}
  False => []

takeWhileFreshness  pred []           fresh
  = ()
takeWhileFreshness  pred (x :: xs) (y_fresh_x, y_fresh_xs) with (pred x)
 takeWhileFreshness pred (x :: xs) (y_fresh_x, y_fresh_xs) | True
  = (y_fresh_x, takeWhileFreshness pred xs y_fresh_xs)
 takeWhileFreshness pred (x :: xs) (y_fresh_x, y_fresh_xs) | False
  = ()


public export
dropWhile : (pred : a -> Bool) -> FreshList a neq -> FreshList a neq

public export
dropWhileFreshness : (pred : a -> Bool) -> (xs : FreshList a neq) ->
  y # xs -> y # dropWhile pred xs


dropWhile pred     []              = []
dropWhile pred ((x :: xs) {fresh}) = case pred x of
  True  => (x :: dropWhile pred xs) {fresh = dropWhileFreshness pred xs fresh}
  False => []

dropWhileFreshness  pred    []     fresh = ()
dropWhileFreshness  pred (x :: xs) (y_neq_x, y_fresh_xs) with (pred x)
 dropWhileFreshness pred (x :: xs) (y_neq_x, y_fresh_xs) | False
   = ()
 dropWhileFreshness pred (x :: xs) (y_neq_x, y_fresh_xs) | True
   = (y_neq_x, dropWhileFreshness pred xs y_fresh_xs)

public export
filter : (pred : a -> Bool) -> FreshList a neq -> FreshList a neq
public export
filterFreshness : (pred : a -> Bool) -> (xs : FreshList a neq) ->
  y # xs -> y # filter pred xs

filter pred     []              = []
filter pred ((x :: xs) {fresh}) = case pred x of
  False => filter pred xs
  True  => (x :: filter pred xs) {fresh = filterFreshness pred xs fresh}

filterFreshness  pred    []     fresh                 = ()
filterFreshness  pred (x :: xs) (y_neq_x, y_fresh_xs) with (pred x)
 filterFreshness pred (x :: xs) (y_neq_x, y_fresh_xs) | False
   =           filterFreshness pred xs y_fresh_xs
 filterFreshness pred (x :: xs) (y_neq_x, y_fresh_xs) | True
   = (y_neq_x, filterFreshness pred xs y_fresh_xs)

public export
decideFreshness : (x : a) -> (decide : (y : a) -> Dec (x `neq` y)) -> (ys : FreshList a neq)
  -> Dec (x # ys)
decideFreshness x decide    []     = Yes ()
decideFreshness x decide (y :: ys) = case decide y of
  No  x_stale_y => No $ x_stale_y . fst
  Yes x_fresh_y    => case decideFreshness x decide ys of
    Yes x_fresh_ys => Yes (x_fresh_y, x_fresh_ys)
    No  x_stale_ys => No $ x_stale_ys . snd

public export
foldl : (f : b -> a -> b) -> b -> FreshList a neq -> b
foldl f x [] = x
foldl f x (y :: ys) = foldl f (x `f` y) ys

public export
foldr : (f : a -> b -> b) -> b -> FreshList a neq -> b
foldr f x [] = x
foldr f x (val :: vals) = (val `f` foldr f x vals)

namespace String
  public export
  (#) : (s,t : String) -> Type
  s # t = ((s == t) === False)

  %hint
  public export
  (#?) : (s,t : String) -> Dec (s # t)
  s  #? t = case (@@(s == t)) of
    (False ** prf) => Yes prf
    (True  ** prf) => No $ \prf' => absurd $ trans (sym prf) prf'

namespace Aux
  public export
  FreshSnoc : {a : Type} -> {neq : Rel a} -> SnocList a -> FreshList a neq -> Type

public export
castAux : (sx : SnocList a) -> (xs : FreshList a neq) ->
  {auto 0 fresh : FreshSnoc {neq} sx xs} -> FreshList a neq

namespace Aux

  FreshSnoc [<] xs = ()
  FreshSnoc (sx :< x) xs = (fresh : x # xs ** FreshSnoc sx ((x :: xs) {fresh}))

castAux     [<]   xs = xs
castAux (sx :< x) xs {fresh}
  = castAux sx ((x :: xs) {fresh = fresh.fst}) {fresh = fresh.snd}

public export
Fresh : {a : Type} -> {neq : Rel a} -> SnocList a -> Type
Fresh {neq} sx = FreshSnoc {neq} sx []

public export
cast : (sx : SnocList a) -> {auto 0 fresh : Fresh {neq} sx} -> FreshList a neq
cast sx = castAux sx []
