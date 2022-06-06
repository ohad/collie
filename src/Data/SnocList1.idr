module Data.SnocList1

import Data.SnocList

%default total

||| A non empty variant of the type of snoc-lists
public export
record SnocList1 (a : Type) where
  constructor (:<)
  tail : SnocList a
  head : a

||| Forget that a snoc-list is non empty
public export
forget : SnocList1 a -> SnocList a
forget (sx :< x) = sx :< x

||| 'fish': Action of lists on snoc-lists
public export
(<><) : SnocList1 a -> List a -> SnocList1 a
sx <>< [] = sx
sx <>< (y :: ys) = (forget sx :< y) <>< ys
