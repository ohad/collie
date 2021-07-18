module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import Decidable.Decidable.Extra
import Data.DPair

infix 4 ::=
public export
(::=) : String -> a -> (String, a)
(::=) = MkPair

public export
Flag : Fields Type
Flag = [ "description" ::= String
       , "default"     ::=  Bool]

public export
Option : Fields Type
Option = ["description"::= String
         , "arguments" ::= Arguments]

public export
data Modifier
  = MkFlag   (Record Prelude.id Flag  )
  | MkOption (Record Prelude.id Option)

public export
flag : String -> {default False defaultVal : Bool} -> Modifier
flag desc = MkFlag $ MkRecord [desc, defaultVal]

public export
option : String -> Arguments -> Modifier
option desc ducer = MkOption $ MkRecord [desc, ducer]

public export
ParsedModifier : Modifier -> Type
ParsedModifier (MkFlag   flg) = Bool
ParsedModifier (MkOption opt) = Carrier (opt.project "arguments").domain

public export
ParsedModifiers : (mods : Fields Modifier) -> Type
ParsedModifiers mods = Record (Maybe . ParsedModifier) mods

public export
updateModifier : (name : String) -> {mod : Modifier} ->
  (new : ParsedModifier mod) ->
  (old : Maybe (ParsedModifier mod)) -> Error (Maybe $ ParsedModifier mod)
updateModifier  name                      new Nothing    = pure $ Just new
{- TODO: currently, overwrite previous flag, but we can do something
better here: customise the behaviour, or parameterise by a partial
monoid -}
updateModifier  name {mod = MkFlag   flg} new (Just old) = pure $ Just new
updateModifier  name {mod = MkOption opt} new (Just old) with ((opt.project "arguments").domain)
 updateModifier name {mod = MkOption opt} new (Just old) | Some d
   = throwE $ "MkOption \{name} set twice"
 updateModifier name {mod = MkOption opt} new (Just old) | ALot ds
   = let _ = openMagma ds in
     pure $ Just $ old <+> new

public export
(.update) : {mods : Fields Modifier} -> (ps : ParsedModifiers mods) ->
  {name : String} -> (pos : name `IsField` mods) ->
  (p : ParsedModifier (field pos)) -> Error (ParsedModifiers mods)
ps.update pos p = MkRecord <$> ps.content.update pos (updateModifier name p)
