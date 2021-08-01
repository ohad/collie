module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import Data.Maybe

infix 4 ::=
public export
(::=) : {0 a : String -> Type} -> (nm : String) -> a nm -> (nm : String ** a nm)
(::=) = MkDPair

public export
Flag : Fields (const Type)
Flag = [ "description" ::=  String
       , "default"     ::=  Bool]

public export
Option : Fields (const Type)
Option = [ "description" ::= String
         , "arguments"   ::= Arguments]

public export
data Modifier : (nm : String) -> Type where
  MkFlag   : Record DPair.snd Flag   -> Modifier nm
  MkOption : Record DPair.snd Option -> Modifier nm

public export
flag : {0 nm : String} ->
       (description : String) ->
       {default False defaultVal : Bool} ->
       Modifier nm
flag desc = MkFlag $ MkRecord [desc, defaultVal]

public export
option : {0 nm : String} ->
         (description : String) ->
         (arguments : Arguments) ->
         Modifier nm
option desc ducer = MkOption $ MkRecord [desc, ducer]

public export
ParsedModifier : (f, g : Type -> Type) -> Modifier nm -> Type
ParsedModifier f g (MkFlag   flg) = f Bool
ParsedModifier f g (MkOption opt) = g $ Carrier (opt.project "arguments").domain

public export
ParsedModifiers : (f, g : Type -> Type) -> (mods : Fields Modifier) -> Type
ParsedModifiers f g mods = Record (\ fld => ParsedModifier f g (snd fld)) mods

public export
updateModifier :
  {name : String} ->
  {mod : Modifier name} ->
  (new : ParsedModifier Prelude.id Prelude.id mod) ->
  (old : ParsedModifier Maybe Maybe mod) ->
  Error (ParsedModifier Maybe Maybe mod)
updateModifier   {mod = MkFlag   flg} new Nothing    = pure $ Just new
updateModifier   {mod = MkOption opt} new Nothing    = pure $ Just new
{- TODO: currently, overwrite previous flag, but we can do something
better here: customise the behaviour, or parameterise by a partial
monoid -}
updateModifier   {mod = MkFlag   flg} new (Just old) = pure $ Just new
updateModifier   {mod = MkOption opt} new (Just old)
  with ((opt.project "arguments").domain)
  updateModifier {mod = MkOption opt} new (Just old) | Some d
    = throwE $ "MkOption \{name} set twice"
  updateModifier {mod = MkOption opt} new (Just old) | ALot ds
    = let _ = openMagma ds in
      pure $ Just $ old <+> new

public export
-- TODO: can we generalise this beyond `Maybe`?
(.update) : {mods : Fields Modifier} ->
  (ps : ParsedModifiers Maybe Maybe mods) ->
  (pos : Any p mods) ->
  (p : ParsedModifier Prelude.id Prelude.id (snd (field pos))) ->
  Error (ParsedModifiers Maybe Maybe mods)
ps.update pos p = MkRecord <$> ps.content.update pos (updateModifier p)

||| All the flags have a default value. If no value has been set then use
||| that default instead.
public export
defaulting : {mods : Fields Modifier} ->
  ParsedModifiers Maybe f mods -> ParsedModifiers Prelude.id f mods
defaulting = map $ \ (str ** mod), val => case mod of
  MkFlag   flg => fromMaybe (flg.project "default") val
  MkOption opt => val

public export
initNothing : {flds : Fields Modifier} -> ParsedModifiers Maybe Maybe flds
initNothing = MkRecord $ tabulate $ \ (str ** mod) => case mod of
  MkFlag   flg => Nothing
  MkOption opt => Nothing
