open import Data.List
open import Data.Product

open import Relation.Binary.PropositionalEquality

module Base.Basics where

  []-++ : ∀ {A : Set}(xs ys : List A) → [] ≡ xs ++ ys → xs ≡ [] × ys ≡ []
  []-++ [] [] refl = refl , refl
  []-++ [] (x ∷ ys) ()
  []-++ (x ∷ xs) ys ()
