module Decidable.Decidable.Extra

import public Decidable.Decidable

public export
toWitness : {prf : Dec a} -> IsYes prf -> a
toWitness {prf = Yes prf} x = prf
