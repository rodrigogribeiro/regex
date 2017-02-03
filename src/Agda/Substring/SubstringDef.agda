open import Data.Char
open import Data.List

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Substring.SubstringDef where

  open import Base.Regex
  open import Prefix.PrefixDef

  data IsSubstring (xs : List Char)(e : Regex) : Set where
    Substring : (ys zs ws : List Char) →
                (eq : xs ≡ ys ++ zs ++ ws) → 
                (wit : zs ∈[ e ] ) →
                IsSubstring xs e

  ¬IsSubstring : ∀ {e} → ¬ IsPrefix [] e → ¬ IsSubstring [] e
  ¬IsSubstring neg (Substring [] zs ws eq wit) = neg (Prefix zs ws eq wit)
  ¬IsSubstring neg (Substring (x ∷ ys) zs ws () wit)

  ¬IsSubstring-∷ : ∀ {e x xs} → ¬ (IsPrefix (x ∷ xs) e)
                              → ¬ (IsSubstring xs e)
                              → ¬ (IsSubstring (x ∷ xs) e)
  ¬IsSubstring-∷ pr pr1 (Substring [] zs ws eq wit) = pr (Prefix zs ws eq wit)
  ¬IsSubstring-∷ pr pr1 (Substring (x₁ ∷ ys) zs ws refl wit) = pr1 (Substring ys zs ws refl wit)
