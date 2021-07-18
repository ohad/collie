module Collie.Usage

import Data.SnocList
import Data.List
import Data.String

import Collie.Core

public export
Printer : Type
Printer = Nat -> List String

export
namedString : String -> String -> Nat -> String
namedString name str width
  = let pad = 2 + width `minus` length name
    in name ++ indent pad str

Show Modifier where
  show (MkFlag   flg) = flg.project "description"
  show (MkOption opt) = opt.project "description"

maxNameWidth : Fields a -> Nat
maxNameWidth xs = foldl (\ u,v => max u (length (fst v))) 0 xs

export
usageModifier : (name : String) -> Modifier -> Nat -> Printer
usageModifier name mod width i = [indent i $ namedString name (show mod) width]

export
usageModifiers : Fields Modifier -> Nat -> Printer
usageModifiers xs width
  = foldr (\(name,mod),u,i => usageModifier name mod width i ++ u i) (const []) xs

export
usageCommand : Command -> Nat -> Printer
usageCommand cmd width i =
  let subWidth : Nat = max (maxNameWidth cmd.subcommands) (maxNameWidth cmd.modifiers) in
  indent i (namedString cmd.name (cmd.description) (2 + width)) ::
    foldr (\ (_, u) => (usageCommand u (subWidth) (2 + i) ++)) [] cmd.subcommands ++
    case (usageModifiers cmd.modifiers subWidth i) of
      [] => []
      xs => [""] ++ xs

export
(.usage) : Command -> String
cmd.usage = unlines $ usageCommand cmd (length cmd.name) 0
