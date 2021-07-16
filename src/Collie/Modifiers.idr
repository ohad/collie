module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import Decidable.Decidable.Extra
import Data.DPair

public export
Flag : Fields Type
Flag = [("description", String), ("default", Bool)]

public export
record Parseducer where
  constructor MkParseducer
  domain : Domain
  parser : Parser d

public export
Option : Fields Type
Option = [("description", String), ("arguments", Parseducer)]

public export
data Modifier
  = MkFlag   (Record Prelude.id Flag  )
  | MkOption (Record Prelude.id Option)

public export
flag : String -> {default False defaultVal : Bool} -> Modifier
flag desc = MkFlag $ MkRecord [desc, defaultVal]

public export
option : String -> Parseducer -> Modifier
option desc ducer = MkOption $ MkRecord [desc, ducer]

public export
ParsedModifier : Modifier -> Type
ParsedModifier (MkFlag   flg) = Bool
ParsedModifier (MkOption opt) = Carrier (opt.project "arguments").domain

public export
ParsedModifiers : (mods : Record (const Modifier) flds) -> Type
ParsedModifiers mods = Record (\a => mods.project ?h1) flds

{-
public export
ParsedModifiers : {args : _} -> (mods : Record args Modifiers.toFields) -> Type
ParsedModifiers mods = Record args (TypeFields $ map (\_ => ParsedModifier) mods)

public export
(.UPDATE) : {args : _} ->
  {mods : RECORD args (Modifiers.toFIELDS {args})} ->
  let flds : FIELDS args
      flds = TypeFIELDS args $ MAP (\u => ParsedModifier) mods
  in
  (ps : RECORD args flds) ->
  {0 arg : String} -> (pos : arg `Elem` args) ->
  (p : ParsedModifier (mods.PROJECT' {flds = Modifiers.toFieldsTabs} pos)) ->
  Error $ RECORD args flds
(q      , ps).UPDATE  Here p {mods = (MkFlag   _, mods)} = pure (p, ps)
(Nothing, ps).UPDATE  Here p {mods = (MkOption _, mods)} = pure (p, ps)
(Just  q, ps).UPDATE  Here p {mods = (MkOption o, mods)} with (fst $ o.project "arguments")
 (Just q, ps).UPDATE  Here p {mods = (MkOption o, mods)} | Some d
   = throwE $ "MkOption \{arg} set twice"
 (Just q, ps).UPDATE  Here p {mods = (MkOption o, mods)} | ALot ds
   = let _ = openMagma $ Maybe.rawMagma ds in
       pure (p <+> (Just q), ps)

(q, ps).UPDATE (There pos) p
  -- We don't have eta for pairs, matching gets us unstuck
  {mods = (mod,mods)}
  = (q,) <$> ps.UPDATE pos p

public export
(.update) : {args : _} -> {mods : Record args Modifiers.toFields} ->
  (ps : ParsedModifiers mods) ->
  (0 arg : String) -> {auto pos : arg `Elem` args} ->
  (p : ParsedModifier (mods.project' {args} {flds = Modifiers.toFieldsTabs} arg {pos})) ->
  Error (ParsedModifiers mods)
ps.update arg {pos} p =
  -- Our applicative doesn't seem dependent enough
  do res <- ps.content.UPDATE pos p
     pure $ MkRecord res
-}
