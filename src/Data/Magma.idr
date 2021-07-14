module Data.Magma

infixr 6 .*.

public export
interface RawMagma where
  constructor MkRawMagma
  Carrier : Type
  (.*.) : Carrier -> Carrier -> Carrier

namespace List
  public export
  rawMagma : (a : Type) -> RawMagma
  rawMagma a = MkRawMagma (List a) (++)

namespace String
  public export
  rawMagma : RawMagma
  rawMagma = MkRawMagma String (++)

namespace Unit
  public export
  rawMagma : RawMagma
  rawMagma = MkRawMagma Unit $ const $ const ()
