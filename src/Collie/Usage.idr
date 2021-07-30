module Collie.Usage

import Data.SnocList
import Data.List
import Data.String

import Collie.Core

public export
Printer : Type
Printer = Nat -> List String

mapFstAndRest : (fst, rest : a -> b) -> List a -> List b
mapFstAndRest fst rest []  = []
mapFstAndRest fst rest (x :: xs) = fst x :: map rest xs

export
namedBlock : (name : String) -> List String -> Nat -> Printer
namedBlock name lines width i
  = let padInitial = 2 + width `minus` length name
        padRest    = 2 + width
    in mapFstAndRest ((indent i name ++) . (indent padInitial))
                     (indent (i + padRest)) lines


(.description) : Modifier str -> List String
(MkFlag   flg).description = flg.project "description"
(MkOption opt).description = opt.project "description"

maxNameWidth : Fields a -> Nat
maxNameWidth xs = foldl (\ u,v => max u (length (fst v))) 0 xs

export
usageModifiers : Fields Modifier -> Nat -> Printer
usageModifiers xs width
  = foldr (\(name ** mod),u,i =>
    namedBlock name mod.description width i ++ u i) (const []) xs

export
usageCommand : {cmdName : String} -> Command cmdName -> Nat -> Printer
usageCommand cmd width i =
  let subWidth : Nat := max (maxNameWidth cmd.subcommands) (maxNameWidth cmd.modifiers) in
  (namedBlock cmdName (cmd.description) width i) ++
  case ( foldr (\ (_ ** u) => (usageCommand u (subWidth) (2 + i) ++)) [] cmd.subcommands
       , usageModifiers cmd.modifiers subWidth (2 + i)) of
    (a, b) => intercalate [""] $ filter ([] /=) [a, b]

export
(.usage) : {cmdName : String} -> Command cmdName -> String
cmd.usage = unlines $ usageCommand cmd (length cmdName) 0
