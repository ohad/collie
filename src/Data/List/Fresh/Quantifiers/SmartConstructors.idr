module Data.List.Fresh.Quantifiers.SmartConstructors

import Data.List.Fresh
import Data.List.Fresh.Quantifiers

import Decidable.Decidable.Extra1
import Decidable.Equality

%default total

public export
mkAny : DecEq a => (x : a) -> {xs : FreshList a neq} ->
        {auto 0 pos : IsYes (x `isElem` xs)} ->
        p x -> Any p xs
mkAny x px = map (\x, Refl => px) (toWitness pos)

public export
(::) : DecEq a =>
         (xpx : (x : a ** p x)) -> {xs : FreshList a neq} ->
         {auto 0 pos : IsYes (xpx.fst `isElem` xs)} ->
         All p (remove (toWitness pos)) -> All p xs
(x ** px) :: pxs = insertWith (\y, Refl => px) (toWitness pos) pxs
