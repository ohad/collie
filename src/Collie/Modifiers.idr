module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import Decidable.Decidable.Extra
import Data.DPair

infix 4 ::=
public export
(::=) : {0 a : String -> Type} -> (nm : String) -> a nm -> (nm : String ** a nm)
(::=) = MkDPair

public export
Flag : Fields (const Type)
Flag = [ "description" ::= String
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
ParsedModifier : Modifier nm -> Type
ParsedModifier (MkFlag   flg) = Bool
ParsedModifier (MkOption opt) = Carrier (opt.project "arguments").domain

public export
ParsedModifiers : (mods : Fields Modifier) -> Type
ParsedModifiers mods = Record (\ fld => Maybe $ ParsedModifier (snd fld)) mods

public export
updateModifier :
  {name : String} ->
  {mod : Modifier name} ->
  (new : ParsedModifier mod) ->
  (old : Maybe (ParsedModifier mod)) ->
  Error (Maybe $ ParsedModifier mod)
updateModifier                        new Nothing    = pure $ Just new
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
(.update) : {mods : Fields Modifier} -> (ps : ParsedModifiers mods) ->
  (pos : Any p mods) ->
  (p : ParsedModifier (snd (field pos))) -> Error (ParsedModifiers mods)
ps.update pos p = MkRecord <$> ps.content.update pos (updateModifier p)
