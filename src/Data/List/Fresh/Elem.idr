module Data.List.Fresh.Elem

import Data.List.Fresh

%default total

public export
data Elem : a -> FreshList a neq -> Type where
  Here  : Elem x ((x :: xs) {fresh})
  There : (pos : Elem y xs) -> Elem y ((x :: xs) {fresh})

export
Uninhabited (Here = There {fresh} e) where
  uninhabited Refl impossible

export
Uninhabited (There {fresh} e = Here) where
  uninhabited Refl impossible

public export
(.recall) : (xs : FreshList a neq) -> (pos : x `Elem` xs) -> a
(x :: xs).recall Here = x
(x :: xs).recall (There pos) = xs.recall pos

public export
recallId : (xs : FreshList a neq) -> (pos : x `Elem` xs) -> xs.recall pos = x
recallId (x :: xs) Here = Refl
recallId (x :: xs) (There pos) = recallId xs pos
