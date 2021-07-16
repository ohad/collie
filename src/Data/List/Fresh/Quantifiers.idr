module Data.List.Fresh.Quantifiers

import Data.List.Fresh
import Data.DPair

namespace Any
  public export
  data Any : (0 p : a -> Type) -> FreshList a neq -> Type where
    Here : {0 xs : FreshList a neq} -> (val : p x) -> {auto fresh : x # xs} ->
      Any p ((x :: xs) {fresh})
    There : {0 xs : FreshList a neq} -> (pos : Any p xs) -> {auto fresh : x # xs} ->
      Any p ((x :: xs) {fresh})

export
Uninhabited (Any {neq} p []) where
  uninhabited _ impossible

namespace All
  public export
  data All : (0 p : a -> Type) -> FreshList a neq -> Type where
    Nil : All p Nil
    (::) : {0 xs : FreshList a neq} -> (val : p x) -> {auto fresh : x # xs} -> (vals : All p xs) ->
      All p ((x :: xs) {fresh})

public export
lookupWithProof : {0 xs : FreshList a neq} -> (pos : Any p xs) -> Exists p
lookupWithProof (Here  val) = Evidence _ val
lookupWithProof (There pos) = lookupWithProof pos

public export 0
lookup : {0 xs : FreshList a neq} -> (pos : Any p xs) -> a
lookup = fst . lookupWithProof

infixr 4 !!

public export
(!!) : (prfs : All p xs) -> (pos : Any q xs) -> p (lookup pos)
px :: pxs !! Here  val = px
px :: pxs !! There pos = pxs !! pos

public export
(.toFreshList) : {xs : FreshList a neq} -> (rec : All p xs) ->
  FreshList (x : a ** p x) (neq `on` (.fst))
public export
(.toFreshListFreshness) : {xs : FreshList a neq} -> (rec : All p xs) ->
  (y # xs) -> (y ** _) # rec.toFreshList

[].toFreshList = []
((val :: vals) {fresh}).toFreshList = ((_ ** val) :: vals.toFreshList) {fresh = ?hs1}

[]           .toFreshListFreshness y_fresh_xs = ()
(val :: vals).toFreshListFreshness (y_fresh_val, y_fresh_vals)
  = (y_fresh_val, vals.toFreshListFreshness y_fresh_vals)

public export
sequence : Applicative f => All {neq} (f . p) xs -> f (All {neq} p xs)
sequence [] = pure []
sequence (val :: vals) = (\x, xs => x :: xs) <$> val <*> sequence vals

public export
any : (decide : (x : a) -> Dec $ p x) -> (xs : FreshList a neq) -> Dec (Any p xs)
any _ [] = No absurd
any decide (x :: xs) = case decide x of
  Yes prf   => Yes $ Here prf
  No not_x  => case any decide xs of
                 Yes prf    => Yes (There prf)
                 No  not_xs => No \case
                   Here val  => not_x val
                   There pos => not_xs pos
