open import Data.Char
open import Data.List
open import Data.Product

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Base.Basics
open import Base.Regex
open import Derivative.Brzozowski
open import Base.EmptynessTest
open import Prefix.PrefixDef

module Prefix.PrefixBrzozowski where
  
  ¬Prefix-∷ : ∀ {e : Regex}{x xs} → ¬ ([] ∈[ e ]) → ¬ (IsPrefix xs ∂[ e , x ]) → ¬ IsPrefix (x ∷ xs) e
  ¬Prefix-∷ ep pcons (Prefix [] zs eq wit)
    = ep wit
  ¬Prefix-∷ ep pcons (Prefix (y ∷ ys) zs refl wit)
    = pcons (Prefix ys zs refl (∂-complete _ _ _ wit))

  IsPrefixDec : ∀ (xs : List Char)(e : Regex) → Dec (IsPrefix xs e)
  IsPrefixDec [] e with ν[ e ]
  IsPrefixDec [] e | yes p = yes (Prefix [] [] refl p)
  IsPrefixDec [] e | no ¬p = no (¬IsPrefix ¬p)
  IsPrefixDec (x ∷ xs) e with ν[ e ]
  IsPrefixDec (x ∷ xs) e | yes p = yes (Prefix [] (x ∷ xs) refl p)
  IsPrefixDec (x ∷ xs) e | no ¬p with IsPrefixDec xs (∂[ e , x ])
  IsPrefixDec (x ∷ xs) e | no ¬p | (yes (Prefix ys zs eq wit))
    = yes (Prefix (x ∷ ys) zs (cong (_∷_ x) eq) (∂-sound _ _ _ wit))
  IsPrefixDec (x ∷ xs) e | no ¬pn | (no ¬p) = no (¬Prefix-∷ ¬pn ¬p)
