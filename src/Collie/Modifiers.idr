module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Data.Record.Ordered.SmartConstructors
import public Collie.Options.Domain

public export
Flag : Fields ["description"]
Flag = TypeFields $ [].insert' Before _ String

public export
Option : Fields ["description", "arguments"]
Option = (Flag).insert AfterHere _ (d : Domain ** Parser d)

public export
data Modifier : (name : String) -> Type where
  MkFlag   : Record _ Flag   -> Modifier name
  MkOption : Record _ Option -> Modifier name

public export
flag : String -> Modifier name
flag str = MkFlag $ [].insert' Before "description" str

public export
option : String -> (d : Domain ** Parser d) -> Modifier name
option str parser = MkOption $ ([].insert' Before    "description" str)
                                  .insert  AfterHere "arguments" parser

public export
toFieldsTabs : {args : ArgList} -> (pos : arg `Elem` args) -> Type
toFieldsTabs = \pos => Modifier (args.recall pos)

public export
toFIELDS : {args : ArgList} -> FIELDS args
toFIELDS = TABULATE args toFieldsTabs

public export
toFields : {args : ArgList} -> Fields args
toFields = tabulate toFieldsTabs

public export
Modifiers : Type
Modifiers = (args : ArgList ** Record args (toFields))

public export
noModifiers : Modifiers
noModifiers = ([] ** [])

public export
ParsedModifier : Modifier arg -> Type
ParsedModifier (MkFlag   flg) = Bool
ParsedModifier (MkOption opt) = Maybe $ Carrier $ fst $ opt.project "arguments"

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
(Just  q, ps).UPDATE  Here p {mods = (MkOption _, mods)} = ?UPDATE_rhs_13
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
