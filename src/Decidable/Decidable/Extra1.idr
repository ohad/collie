module Decidable.Decidable.Extra

import public Decidable.Decidable

public export
toWitness : {prf : Dec a} -> (0 _ : IsYes prf) -> a
toWitness {prf = Yes prf} x = prf
