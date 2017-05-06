open import Data.Char
open import Data.List
open import Data.Product

open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Base.Basics
open import Base.Regex
open import BitCoded.BitRegex
open import Prefix.PrefixDef

module Prefix.BitPrefix where


  []-erase : ∀ e → ¬ ([] ∈[[ e ]]) → ¬ ([] ∈[ erase e ])
  []-erase empty pr ()
  []-erase (eps x) pr prf = pr (eps x)
  []-erase (char x c) pr ()
  []-erase (choice x e e') pr (.(erase e') +L prf) = []-erase e (λ z → pr (inl e' x z)) prf
  []-erase (choice x e e') pr (.(erase e) +R prf) = []-erase e' (λ z → pr (inr e x z)) prf
  []-erase (cat x e e₁) pr (_∙_⇒_ {xs = xs}{ys = ys}prf prf' eq) with []-++ xs ys eq
  ...| eq1 , eq2 rewrite eq1 | eq2 = pr (cat x (bitSemComplete' _ prf) (bitSemComplete' _ prf') refl)
  []-erase (star x e) pr ((.(erase e ∙ erase e ⋆) +L prf) ⋆) = pr (star-[] x)
  []-erase (star x e) pr ((.ε +R prf) ⋆) = pr (star-[] x)

  ¬Prefix-∷ : ∀ {e x xs} → ¬ ([] ∈[[ e ]]) → ¬ (IsPrefix xs (erase (bitDeriv e x))) → ¬ IsPrefix (x ∷ xs) (erase e)
  ¬Prefix-∷ ep pcons (Prefix [] zs eq wit)
    = ep (bitSemComplete' _ wit) 
  ¬Prefix-∷ ep pcons (Prefix (y ∷ ys) zs refl wit)
    = pcons (Prefix ys zs refl (bitSemSound (bitDerivComplete y ys _ (bitSemComplete' _ wit))))
 
  IsPrefixDec : ∀ (xs : List Char)(e : BitRegex) → Dec (IsPrefix xs (erase e))
  IsPrefixDec [] e with nullDec e
  ...| yes p = yes (Prefix [] [] refl (bitSemSound p))
  ...| no p  = no (¬IsPrefix ([]-erase _ p)) 
  IsPrefixDec (x ∷ xs) e with nullDec e
  ...| yes p = yes (Prefix [] (x ∷ xs) refl (bitSemSound p))
  ...| no  p with IsPrefixDec xs (bitDeriv e x)
  ...| yes (Prefix ys zs eq wit) = yes (Prefix (x ∷ ys) zs (cong (_∷_ x) eq) (bitSemSound (bitDerivSound x ys _ (bitSemComplete' _ wit))))
  ...| no  q = no (¬Prefix-∷ p q)
