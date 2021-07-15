module Collie.Options.Domain

import Data.Magma
import public Control.Monad.Error.Either
import public Control.Monad.Identity
import public Control.Monad.Error.Interface

public export
Error : Type -> Type
Error = EitherT String Identity

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
Parser d = String -> Error $ Carrier d
