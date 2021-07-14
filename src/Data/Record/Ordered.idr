||| An ordered record is a record whose field names have to appear in
||| a fixed order, but must otherwise be distinct.
module Data.Record.Ordered

import Data.List.Fresh
import Data.List.Fresh.Elem
import Data.Fin

-- TODO: move to an stdlib package
namespace Pair
  public export
  data EtaLaw : (a,b) -> Type where
    Eta : (0 x : a) -> (0 y : b) -> EtaLaw (x,y)

  public export
  eta : (0 p : (a,b)) -> EtaLaw p
  eta (x,y) = Eta x y



public export
ArgList : Type
ArgList = FreshList String String.(#)

public export
FIELDS : (args : ArgList) -> Type
FIELDS [] = ()
FIELDS (arg :: args) = (Type , FIELDS args)

public export
record Fields (Args : ArgList) where
  constructor MkFields
  fields : FIELDS Args

public export
(.LOOKUP) : {0 args : ArgList} -> (fs : FIELDS args) -> (pos : arg `Elem` args) -> Type
-- Avoid matching on fields, OTT style, and we could avoid eta laws
(.LOOKUP) flds  Here       = fst flds
(.LOOKUP) flds (There pos) = (snd flds).LOOKUP pos

public export
(.lookup) : {0 args : ArgList} -> (fs : Fields args) -> (pos : arg `Elem` args) -> Type
(.lookup) flds pos = flds.fields.LOOKUP pos

namespace Field
  public export
  TABULATE : (args : ArgList) -> (f : {arg : String} -> (pos : arg `Elem` args) -> Type) ->
    FIELDS args
  TABULATE    []     f = ()
  TABULATE (x :: xs) f = (f Here, TABULATE xs (f . There))

  public export
  tabulate : {args : ArgList} -> (f : {arg : String} -> (pos : arg `Elem` args) -> Type) ->
    Fields args
  tabulate = MkFields . TABULATE args

  public export
  TYPES : (args : ArgList) -> FIELDS args
  TYPES args = TABULATE args $ const $ Type

  public export
  Types : {args : ArgList} -> Fields args
  Types = MkFields (TYPES args)

infix 5 ||>, |>

public export
(||>) : {args : ArgList} -> (f : Type -> Type) -> FIELDS args -> FIELDS args
(||>) {args =     []     } f       flds  = ()
(||>) {args = arg :: args} f (fld, flds) = (f fld, f ||> flds)

public export
(|>) : {args : ArgList} -> (f : Type -> Type) -> Fields args -> Fields args
f |> flds = MkFields $ f ||> flds.fields

public export
RECORD : (args : ArgList) -> (f : FIELDS args) -> Type
RECORD    []           flds  = Unit
-- Avoid matching on fields, OTT style, and we could avoid eta laws
RECORD (x :: xs) flds = (fst flds, RECORD xs (snd flds))

public export
record Record (args : ArgList) (flds : Fields args) where
  constructor MkRecord
  content : RECORD args flds.fields

public export
data Space : (args : ArgList) -> Type where
  Before : Space args
  AfterHere : Space ((arg :: args) {fresh})
  AfterThere : Space args -> Space ((arg :: args) {fresh})


namespace FreshList
  public export
  (.insert) : (args : ArgList) -> Space args -> (arg : String) -> {auto fresh : arg # args} ->
    ArgList

  public export
  (.insertFreshness) : (args : ArgList) -> (pos : Space args) -> (arg : String) ->
    {auto fresh : arg # args} ->
    {auto arg0_fresh_arg : arg0 # arg} ->
    {auto arg0_fresh_args : arg0 # args} ->
    arg0 # args.insert pos arg {fresh}

  args          .insert  Before          arg = arg :: args
  (arg0 :: args).insert  AfterHere       arg = arg0 :: arg :: args
  (arg0 :: args).insert (AfterThere pos) arg {fresh}
    = (arg0 :: args.insert pos arg)
      {fresh = args.insertFreshness pos arg}

  args          .insertFreshness  Before          arg = (arg0_fresh_arg, arg0_fresh_args)
  (arg1 :: args).insertFreshness  AfterHere       arg
    = (fst arg0_fresh_args, (arg0_fresh_arg, snd arg0_fresh_args))
  (arg1 :: args).insertFreshness (AfterThere pos) arg
    = (fst arg0_fresh_args , args.insertFreshness pos arg)

namespace Field
  public export
  (.INSERT) : FIELDS args -> (pos : Space args) ->
    (arg : String) -> {auto fresh : arg # args} -> Type ->
    FIELDS (args.insert pos arg {fresh})
  flds        .INSERT Before           arg fld = (fld, flds)
  -- Again, avoiding matching on flds OTT style will keep us unstuck
  flds.INSERT AfterHere        arg fld = (fst flds, fld, snd flds)
  flds.INSERT (AfterThere pos) arg fld = (fst flds, (snd flds).INSERT pos arg fld)

  public export
  (.insert) : Fields args -> (pos : Space args) ->
    (arg : String) -> {auto fresh : arg # args} -> Type ->
    Fields (args.insert pos arg {fresh})
  flds.insert pos arg fld = MkFields $ flds.fields.INSERT pos arg fld

namespace Record
  public export
  (.INSERT) : RECORD args flds -> (pos : Space args) ->
    (arg : String) -> {auto 0 fresh : arg # args} -> {0 fld : Type} -> (val : fld) ->
    RECORD (args.insert pos arg {fresh}) (flds.INSERT pos arg {fresh} fld)
  rec         .INSERT  Before          arg val = (val, rec)
  (val0, rec) .INSERT (AfterHere     ) arg val = (val0, val, rec)
  (val0, rec) .INSERT (AfterThere pos) arg val = (val0, rec.INSERT pos arg val)

  public export
  (.insert) : Record args flds -> (pos : Space args) ->
    (arg : String) -> {auto 0 fresh : arg # args} -> {0 fld : Type} -> (val : fld) ->
    Record (args.insert pos arg {fresh}) (flds.insert pos arg {fresh} fld)
  rec.insert pos arg val = MkRecord $ rec.content.INSERT pos arg val

public export
FOLDR : {args : ArgList} ->
  {ty : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (acc: {0 arg : String} -> (pos : arg `Elem` args) -> ty pos -> a -> a) ->  a ->
  RECORD args (TABULATE args ty) -> a
FOLDR acc e rec {args = []} = e
FOLDR acc e (val0, rec) {args = (arg0 :: args)} = acc Here val0 $
  FOLDR (\u,x => acc (There u) x) e rec {args}

public export
foldr : {args : ArgList} ->
  {ty : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (acc: {0 arg : String} -> (pos : arg `Elem` args) -> ty pos -> a -> a) ->  a ->
  Record args (tabulate ty) -> a
foldr acc e  = FOLDR acc e . (.content)

public export
(.PROJECT) : (rec : RECORD args flds) -> (pos : arg `Elem` args) -> flds.LOOKUP pos
(val, rec).PROJECT  Here       = val
(val, rec).PROJECT (There pos) = rec.PROJECT pos


public export
(.project) : (rec : Record args flds) -> (pos : arg `Elem` args) -> flds.lookup pos
rec.project pos = rec.content.PROJECT pos

public export
(.PROJECT') : {0 flds : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (rec : RECORD args (TABULATE args flds)) -> (pos : arg `Elem` args) -> flds pos
(val, rec).PROJECT'  Here       = val
(val, rec).PROJECT' (There pos) = rec.PROJECT' pos

-- A record of Types encodes a Fields, allowing us to type nested records

public export
TypeFIELDS : (args : ArgList) -> (rec : RECORD args (TYPES args)) -> FIELDS args
TypeFIELDS      []       rec        = ()
TypeFIELDS (arg :: args) (val, rec) = (val, TypeFIELDS args rec)

public export
TypeFields : {args : ArgList} -> (rec : Record args Types) -> Fields args
TypeFields = MkFields . (TypeFIELDS _) . (.content)

public export
TABULATE : {args : ArgList} -> {0 flds : FIELDS args} ->
  (vals : {0 arg : String} -> (pos : arg `Elem` args) -> flds.LOOKUP pos) ->
  RECORD args flds
TABULATE {args =     []     } vals = ()
TABULATE {args = fld :: flds} vals = (vals Here, TABULATE (\u => vals (There u)))

public export
tabulate : {args : ArgList} -> {0 flds : Fields args} ->
  (vals : {0 arg : String} -> (pos : arg `Elem` args) -> flds.lookup pos) ->
  Record args flds
tabulate = MkRecord . TABULATE

public export
TABULATE' : {args : ArgList} -> {0 flds : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (vals : {0 arg : String} -> (pos : arg `Elem` args) -> flds pos) ->
  RECORD args (TABULATE args flds)
TABULATE' {args =     []     } vals = ()
TABULATE' {args = fld :: flds} vals = (vals Here, TABULATE' (\u => vals (There u)))

public export
tabulate' : {args : ArgList} -> {0 flds : {0 arg : String} -> (pos : arg `Elem` args) -> Type} ->
  (vals : {0 arg : String} -> (pos : arg `Elem` args) -> flds pos) ->
  Record args (tabulate flds)
tabulate' = MkRecord . TABULATE'


{- TODO: gallais's MRecord, ought to be easy with map -}
public export
PartialRECORD : (args : ArgList) -> (flds : FIELDS args) -> Type
PartialRECORD    []     flds = Unit
PartialRECORD (x :: xs) flds = ?PartialRECORD_rhs_2
