module Collie.Modifiers

import Data.Magma
import public Data.Record.Ordered
import public Collie.Options.Domain
import public Collie.Error
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
ParsedModifierT : (f, g : Type -> Type) -> Modifier nm -> Type
ParsedModifierT f g (MkFlag   flg) = f Bool
ParsedModifierT f g (MkOption opt) = ParsedArgumentsT g (opt.project "arguments")

public export
ParsedModifier : Modifier nm -> Type
ParsedModifier (MkFlag   flg) = Bool
ParsedModifier (MkOption opt) = ParsedArguments (opt.project "arguments")

public export
ParsedModifiersT : (f, g : Type -> Type) -> (mods : Fields Modifier) -> Type
ParsedModifiersT f g mods = Record (\ fld => ParsedModifierT f g (snd fld)) mods

public export
ParsedModifiers : (mods : Fields Modifier) -> Type
ParsedModifiers mods = Record (\ fld => ParsedModifier (snd fld)) mods

public export
updateModifier :
  {name : String} ->
  {mod : Modifier name} ->
  (new : ParsedModifierT Prelude.id Prelude.id mod) ->
  (old : ParsedModifierT Maybe Maybe mod) ->
  Error (ParsedModifierT Maybe Maybe mod)
updateModifier   {mod = MkFlag   flg} new Nothing    = pure $ Just new
updateModifier   {mod = MkOption opt} new Nothing    = pure $ Just new
{- TODO: currently, overwrite previous flag, but we can do something
better here: customise the behaviour, or parameterise by a partial
monoid -}
updateModifier   {mod = MkFlag   flg} new (Just old) = pure $ Just new
updateModifier   {mod = MkOption opt} new (Just old)
  with ((opt.project "arguments").domain)
  updateModifier {mod = MkOption opt} new (Just old) | Some d
    = throwE $ OptionSetTwice name
  updateModifier {mod = MkOption opt} new (Just old) | ALot ds
    = let _ = openMagma ds in
      pure $ Just $ old <+> new

public export
-- TODO: can we generalise this beyond `Maybe`?
(.update) : {mods : Fields Modifier} ->
  (ps : ParsedModifiersT Maybe Maybe mods) ->
  (pos : Any p mods) ->
  (p : ParsedModifierT Prelude.id Prelude.id (snd (field pos))) ->
  Error (ParsedModifiersT Maybe Maybe mods)
ps.update pos p = MkRecord <$> ps.content.update pos (updateModifier p)

||| All the flags have a default value. If no value has been set then use
||| that default instead.
public export
defaulting : {mods : Fields Modifier} ->
  ParsedModifiersT Maybe f mods -> ParsedModifiersT Prelude.id f mods
defaulting = map $ \ (str ** mod), val => case mod of
  MkFlag   flg => fromMaybe (flg.project "default") val
  MkOption opt => val

namespace Arguments

  public export
  finalising :
    Lazy ErrorMsg ->
    (args : Arguments) ->
    ParsedArgumentsT Maybe args ->
    Error (ParsedArguments args)
  finalising err args val with (args.required)
    finalising err args val | True  = case val of
      Nothing => throwE err
      Just val => pure val
    finalising err args val | False = pure val

namespace Modifier

  public export
  finalising :
    {nm : String} ->
    (mod : Modifier nm) ->
    ParsedModifierT Maybe Maybe mod ->
    Error (ParsedModifier mod)
  finalising (MkFlag   flg) val = pure $ fromMaybe (flg.project "default") val
  finalising (MkOption opt) val
    = finalising
      (MissingOption nm)
      (opt.project "arguments")
      val

||| Setting the flags to their default value and ensuring that the required
||| options are passed.
public export
finalising :
  {mods : Fields Modifier} ->
  ParsedModifiersT Maybe Maybe mods ->
  Error (ParsedModifiers mods)
finalising = traverse $ \ (str ** mod) => finalising mod

public export
initNothing : {flds : Fields Modifier} -> ParsedModifiersT Maybe Maybe flds
initNothing = MkRecord $ tabulate $ \ (str ** mod) => case mod of
  MkFlag   flg => Nothing
  MkOption opt => Nothing
