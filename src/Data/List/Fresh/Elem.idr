module Data.List.Fresh.Elem

import Data.List.Fresh

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
