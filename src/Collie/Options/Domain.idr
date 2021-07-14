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
  None :                    Domain
  Some : (d  : Type    ) -> Domain
  ALot : (ds : RawMagma) -> Domain

public export
elimDomain : {p : Domain -> Type} ->
  (dNone :                    p  None    ) ->
  (dSome : (d  : Type    ) -> p (Some d )) ->
  (dALot : (ds : RawMagma) -> p (ALot ds)) ->
  (d : Domain) -> p d
elimDomain dNone dSome dALot (None   ) = dNone
elimDomain dNone dSome dALot (Some d ) = dSome d
elimDomain dNone dSome dALot (ALot ds) = dALot ds

public export
Carrier : Domain -> Type
Carrier = elimDomain Unit id (\ds => Magma.Carrier @{ds})

public export
Parser : Domain -> Type
Parser d = String -> Error $ Carrier d
