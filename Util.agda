module Util where

open import Agda.Primitive renaming (_⊔_ to _~U~_) public

variable
  l l1 l2 l3 l4 : Level
  A B C K J L : Set l

data Bool : Set where
  true : Bool
  false : Bool

data _or_ (A B : Set l) : Set l where
  left : A -> A or B
  right : B -> A or B

data _===_ {l : Level} {A : Set l} (a : A) : A -> Set l where
  refl : a === a

record Eq (A : Set l) : Set l where
  field
    _==_ : A -> A -> Bool
open Eq {{...}} public

data <U> {l : Level} : Set l where
  unit : <U>
