module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import Data.Maybe

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
ParsedModifier : (f, g : Type -> Type) -> Modifier -> Type
ParsedModifier f g (MkFlag   flg) = f Bool
ParsedModifier f g (MkOption opt) = g (Carrier (opt.project "arguments").domain)

public export
ParsedModifiers : (f, g : Type -> Type) -> (mods : Fields Modifier) -> Type
ParsedModifiers f g mods = Record (ParsedModifier f g) mods

||| All the flags have a default value. If no value has been set then use
||| that default instead.
public export
defaulting : {mods : Fields Modifier} ->
  ParsedModifiers Maybe f mods -> ParsedModifiers Prelude.id f mods
defaulting = map $ \ str, mod, val => case mod of
  MkFlag   flg => fromMaybe (flg.project "default") val
  MkOption opt => val

public export
initNothing : {flds : Fields Modifier} -> ParsedModifiers Maybe Maybe flds
initNothing = MkRecord $ tabulate $ \ (str, mod) => case mod of
  MkFlag   flg => Nothing
  MkOption opt => Nothing

public export
updateModifier : (name : String) -> {mod : Modifier} ->
  (new : ParsedModifier Prelude.id Prelude.id mod) ->
  (old : ParsedModifier Maybe Maybe mod) ->
  Error (ParsedModifier Maybe Maybe mod)
updateModifier  name {mod = MkFlag   flg} new Nothing    = pure (Just new)
updateModifier  name {mod = MkOption opt} new Nothing    = pure (Just new)
{- TODO: currently, overwrite previous flag, but we can do something
better here: customise the behaviour, or parameterise by a partial
monoid -}
updateModifier  name {mod = MkFlag   flg} new (Just old) = pure (Just new)
updateModifier  name {mod = MkOption opt} new (Just old) with ((opt.project "arguments").domain)
 updateModifier name {mod = MkOption opt} new (Just old) | Some d
   = throwE $ "MkOption \{name} set twice"
 updateModifier name {mod = MkOption opt} new (Just old) | ALot ds
   = let _ = openMagma ds in
     pure (Just $ old <+> new)

public export
-- TODO: can we generalise this beyond `Maybe`?
(.update) : {mods : Fields Modifier} ->
  (ps : ParsedModifiers Maybe Maybe mods) ->
  {name : String} -> (pos : name `IsField` mods) ->
  (p : ParsedModifier Prelude.id Prelude.id (field pos)) ->
  Error (ParsedModifiers Maybe Maybe mods)
ps.update pos p = MkRecord <$> ps.content.update pos (updateModifier name p)
