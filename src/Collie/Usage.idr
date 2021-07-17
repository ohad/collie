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
  = let pad = 1 + width `minus` length name
    in name ++ indent pad str

Show Modifier where
  show (MkFlag   flg) = flg.project "description"
  show (MkOption opt) = opt.project "description"

export
usageModifier : (name : String) -> Modifier -> Nat -> Printer
usageModifier name mod i width = [indent i $ namedString name (show mod) width]

export
usageModifiers : Fields Modifier -> Printer
usageModifiers xs
  = let width : Nat = foldl (\ u,v => max u (length (fst v))) 0 xs
    in foldr (\(name,mod),u,i => usageModifier name mod i width ++ u i) (const []) xs

export
usageCommand : Command -> Printer
usageCommand cmd i =
  indent i (namedString cmd.name (cmd.description) (length cmd.name)) ::
    foldr (\ (_, u) => (usageCommand u (2 + i) ++)) [] cmd.subcommands ++
    (usageModifiers cmd.modifiers (2 + i))

export
(.usage) : Command -> String
cmd.usage = unlines $ usageCommand cmd 0
