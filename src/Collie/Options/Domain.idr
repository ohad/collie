module Collie.Options.Domain

import Data.Magma
import Collie.Error

%default total

public export
data Domain : Type where
  Some : (d  : Type    ) -> Domain
  ALot : (ds : RawMagma) -> Domain

public export
elimDomain : {p : Domain -> Type} ->
  (dSome : (d  : Type    ) -> p (Some d )) ->
  (dALot : (ds : RawMagma) -> p (ALot ds)) ->
  (d : Domain) -> p d
elimDomain dSome dALot (Some d ) = dSome d
elimDomain dSome dALot (ALot ds) = dALot ds

public export
Carrier : Domain -> Type
Carrier = elimDomain id (\ds => ds.Carrier)

public export
Parser : Domain -> Type
Parser d = String -> Either String $ Carrier d

public export
record Arguments where
  constructor MkArguments
  required  : Bool
  domain    : Domain
  rawParser : Parser domain

public export
(.parser) : (arg : Arguments) -> String -> Error (Carrier arg.domain)
arg .parser x = fromEither $ mapFst CouldNotParse (arg.rawParser x)

public export
ParsedArgumentsT : (f : Type -> Type) -> Arguments -> Type
ParsedArgumentsT f ducer = f $ Carrier ducer.domain

public export
ParsedArguments : Arguments -> Type
ParsedArguments ducer
  = ParsedArgumentsT
    (if ducer.required then id else Maybe)
    ducer
