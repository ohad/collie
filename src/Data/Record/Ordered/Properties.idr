module Data.Record.Ordered.Properties

import Data.Record.Ordered

export
lookupTABULATE : {args : ArgList} -> (flds : {0 arg : String} -> (pos : arg `Elem` args) -> Type) ->
  (pos : arg `Elem` args) -> (TABULATE args flds).LOOKUP pos = flds pos
lookupTABULATE flds Here = Refl
lookupTABULATE flds (There pos) = lookupTABULATE (\u => flds (There u)) pos

export
lookupTabulate : {args : ArgList} -> (flds : {0 arg : String} -> (pos : arg `Elem` args) -> Type) ->
  (pos : arg `Elem` args) -> (tabulate flds).lookup pos = flds pos
lookupTabulate = lookupTABULATE
