open import Data.Char
open import Data.List

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Substring.BitSubstring where

  open import Base.Regex
  open import BitCoded.BitRegex
  open import Prefix.BitPrefix
  open import Prefix.PrefixDef
  open import Substring.SubstringDef


  IsSubstringDec' : ∀ (xs : List Char)(e : BitRegex) → Dec (IsSubstring xs (erase e))
  IsSubstringDec' [] e with nullDec e
  ...| yes p = yes (Substring [] [] [] refl (bitSemSound p))
  ...| no  p = no (¬IsSubstring (¬IsPrefix ([]-erase e p)))
  IsSubstringDec' (x ∷ xs) e with IsPrefixDec (x ∷ xs) e
  ...| yes (Prefix ys zs eq wit) = yes (Substring [] ys zs eq wit)
  ...| no  p with IsSubstringDec' xs e
  ...| yes (Substring ys zs ws eq wit) = yes (Substring (x ∷ ys) zs ws (cong (_∷_ x) eq) wit)
  ...| no  pr = no (¬IsSubstring-∷ p pr)


  IsSubstringDec : ∀ (xs : List Char)(e : Regex) → Dec (IsSubstring xs e)
  IsSubstringDec xs e = subst (λ e' → Dec (IsSubstring xs e')) (internalize-erase e) (IsSubstringDec' xs (internalize e))
