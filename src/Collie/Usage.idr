module Collie.Usage

import Data.SnocList
import Data.List
import Data.String

import Collie.Core

import Data.SnocList
import Data.String

reflow : (width : Nat) -> String -> List String
reflow w = map concat . init . (intersperse " ") . words
  where
    -- shift the accumulator into a line, removing the final " ", if present
    shift : SnocList String -> List String
    shift (sx :< " ") = sx <>> []
    shift sx = sx <>> []

    init : List String -> List (List String)
    go : Nat -> SnocList String -> List String -> List (List String)

    init [] = []
    init (" " :: xs) = init xs -- remove initial space
    init (x :: xs) = go (w `minus` length x) [< x] xs

    go Z acc xs        = (shift acc) :: init xs
    go n acc []        = [shift acc]
    go n acc (x :: xs) =
      let l = length x in
      if n < l then (shift acc) :: init (x :: xs)
      else go (n `minus` l) (acc :< x) xs

public export
Printer : Type
Printer = Nat -> List String

mapFstAndRest : (fst, rest : a -> b) -> List a -> List b
mapFstAndRest fst rest []  = []
mapFstAndRest fst rest (x :: xs) = fst x :: map rest xs

export
namedBlock : (name : String) -> String -> (nameWidth, maxWidth : Nat) -> Printer
namedBlock name text nameWidth maxWidth i
  = let padInitial = 2 + nameWidth `minus` length name
        padRest    = 2 + nameWidth
    in mapFstAndRest ((indent i name ++) . (indent padInitial))
                     (indent (i + padRest))
                     (concat $ map (\u => if i + padRest + length u > maxWidth
                                          then reflow (maxWidth `minus` (i + padRest)) u
                                          else [u]) $ lines text)


(.description) : Modifier str -> String
(MkFlag   flg).description = flg.project "description"
(MkOption opt).description = opt.project "description"

maxNameWidth : Fields a -> Nat
maxNameWidth xs = foldl (\ u,v => max u (length (fst v))) 0 xs

export
usageModifiers : Fields Modifier -> (nameWidth, maxWidth : Nat) -> Printer
usageModifiers xs nameWidth maxWidth
  = foldr (\(name ** mod),u,i =>
    namedBlock name mod.description nameWidth maxWidth i ++ u i) (const []) xs

export
usageCommand : {cmdName : String} -> Command cmdName -> (nameWidth, maxWidth : Nat) -> Printer
usageCommand cmd nameWidth maxWidth i =
  let subWidth : Nat := max (maxNameWidth cmd.subcommands) (maxNameWidth cmd.modifiers) in
  (namedBlock cmdName cmd.description nameWidth maxWidth i) ++
  case ( foldr (\ (_ ** u) => (usageCommand u subWidth maxWidth (2 + i) ++)) [] cmd.subcommands
       , usageModifiers cmd.modifiers subWidth maxWidth (2 + i)) of
    (a, b) => intercalate [""] $ filter ([] /=) [a, b]

export
(.usage) : {cmdName : String} -> {default 80 maxWidth : Nat} -> Command cmdName -> String
cmd.usage = unlines $ usageCommand cmd (length cmdName) maxWidth 0
