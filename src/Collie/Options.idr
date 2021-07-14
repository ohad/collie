module Collie.Options

import Data.List.Elem
import Data.Void

import public Collie.Options.Domain

public export
Name : Type
Name = String

public export
record Option where
  constructor MkOption
  name        : Name
  description : String
  flag        : String
  optional    : Bool
  domain      : Domain
  parser      : Parser domain

public export
NotIn : a -> List a -> Type
NotIn y [] = Unit
NotIn y (x :: xs) = (Uninhabited (y === x), NotIn y xs)

public export
data OptionsOver : List Name -> Type where
  Nil  : OptionsOver []
  (::) : (opt : Option) -> (opts : OptionsOver names) ->
         opt.name `NotIn` names => OptionsOver (opt.name :: names)

public export
index : (n `Elem` ns) -> OptionsOver ns -> Option
index  Here       (opt :: opts) = opt
index (There pos) (opt :: opts) = index pos opts

public export
indexSpec : (pos : n `Elem` ns) -> (opts : OptionsOver ns) -> (index pos opts).name = n
indexSpec  Here       (opt :: opts) = Refl
indexSpec (There pos) (opt :: opts) = indexSpec pos opts

public export
record Options where
  constructor MkOptions
  support : List Name
  options : OptionsOver support

public export
Mode : (args : Options) -> Type
--Mode args = (arg : Option) -> (prf : arg.name `Elem` support) -> Type
