open import Data.Char
open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Prefix.PrefixDef where
  open import Base.Basics
  open import Base.Regex

   
  -- data type for witness of a prefix of a regex match

  data IsPrefix (xs : List Char)(e : Regex) : Set where
    Prefix : ∀ (ys zs : List Char)
               (eq : xs ≡ ys ++ zs)
               (wit : ys ∈[ e ]) → IsPrefix xs e


  ¬IsPrefix : {e : Regex} → ¬ ([] ∈[ e ]) → ¬ IsPrefix [] e
  ¬IsPrefix pe (Prefix ys zs eq wit) with []-++ ys zs eq
  ...| refl , refl = pe wit

