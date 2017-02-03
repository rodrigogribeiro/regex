open import Algebra

open import Data.Char
open import Data.List                               hiding (any)
open import Data.List.Any
open import Data.List.Properties
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Derivative.Antimirov
open import Base.EmptynessTest
open import Prefix.PrefixDef
open import Base.Regex

module Prefix.PrefixAntimirov where


  Any-lemma : ∀ {ys e'} es → ys ∈[ e' ] → e' ∈ es → ys ∈⟨ es ⟩
  Any-lemma [] pr ()
  Any-lemma (x ∷ es) pr (here refl) = Here pr
  Any-lemma (x ∷ es) pr (there pr1) = There (Any-lemma es pr pr1)

  module LC = Monoid (Data.List.monoid Char)

  Any-Prefix : ∀ {ys zs} es → ys ∈⟨ es ⟩ → Any (IsPrefix (ys ++ zs)) es
  Any-Prefix [] ()
  Any-Prefix (x ∷ es) (Here x₁) = here (Prefix _ _ refl x₁)
  Any-Prefix (x ∷ es) (There pr) = there (Any-Prefix es pr)

  Any-Prefix-∷ : ∀ {x xs e} → ¬ ([] ∈[ e ]) → ¬ Any (IsPrefix xs) ∇[ e , x ] → ¬ IsPrefix (x ∷ xs) e
  Any-Prefix-∷ pr pr1 (Prefix [] zs eq wit) = pr wit
  Any-Prefix-∷ {e = e} pr pr1 (Prefix (x₁ ∷ ys) zs refl wit) with ∇-complete _ wit
  ...| k = pr1 (Any-Prefix ∇[ e , x₁ ] k)

  IsPrefixDec : ∀ (xs : List Char)(e : Regex) → Dec (IsPrefix xs e)
  IsPrefixDec [] e with ν[ e ]
  IsPrefixDec [] e | yes p = yes (Prefix [] [] refl p)
  IsPrefixDec [] e | no ¬p = no (¬IsPrefix ¬p)
  IsPrefixDec (x ∷ xs) e with ν[ e ]
  IsPrefixDec (x ∷ xs) e | yes p = yes (Prefix [] (x ∷ xs) refl p)
  IsPrefixDec (x ∷ xs) e | no ¬p with any (IsPrefixDec xs) ∇[ e , x ]
  IsPrefixDec (x ∷ xs) e | no ¬p | (yes p) with find p
  IsPrefixDec (x ∷ .(ys ++ zs)) e | no ¬p | (yes p) | (e' , e'∈es , Prefix ys zs refl wit)
    = yes (Prefix (x ∷ ys) zs refl (∇-sound e (Any-lemma ∇[ e , x ] wit e'∈es)))
  IsPrefixDec (x ∷ xs) e | no ¬p₁ | (no ¬p) = no (Any-Prefix-∷ ¬p₁ ¬p)

