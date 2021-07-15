module Collie.Modifiers

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
toFields : {args : ArgList} -> Fields args
toFields = tabulate \pos => Modifier (args.recall pos)

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
