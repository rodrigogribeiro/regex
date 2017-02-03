open import Data.Char
open import Data.List

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Substring.SubstringBrzozowski where

  open import Base.Regex
  open import Base.EmptynessTest
  open import Derivative.Brzozowski
  open import Prefix.PrefixBrzozowski
  open import Prefix.PrefixDef
  open import Substring.SubstringDef


  IsSubstringDec : ∀ (xs : List Char)(e : Regex) → Dec (IsSubstring xs e)
  IsSubstringDec [] e with ν[ e ]
  IsSubstringDec [] e | yes p = yes (Substring [] [] [] refl p)
  IsSubstringDec [] e | no ¬p = no (¬IsSubstring (¬IsPrefix ¬p))
  IsSubstringDec (x ∷ xs) e with IsPrefixDec (x ∷ xs) e
  IsSubstringDec (x ∷ xs) e | yes (Prefix ys zs eq wit) = yes (Substring [] ys zs eq wit)
  IsSubstringDec (x ∷ xs) e | no ¬p with IsSubstringDec xs e
  IsSubstringDec (x ∷ xs) e | no ¬p | (yes (Substring ys zs ws eq wit))
    = yes (Substring (x ∷ ys) zs ws (cong (_∷_ x) eq) wit)
  IsSubstringDec (x ∷ xs) e | no ¬p₁ | (no ¬p) = no (¬IsSubstring-∷ ¬p₁ ¬p)
