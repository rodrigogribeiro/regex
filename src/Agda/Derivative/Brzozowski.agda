open import Data.Char
open import Data.Empty
open import Data.List

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Base.Regex
open import Derivative.Smart
open import Base.EmptynessTest

module Derivative.Brzozowski where

  infix 7 ∂[_,_]

  ∂[_,_] : Regex → Char → Regex
  ∂[ ∅ , c ] = ∅
  ∂[ ε , c ] = ∅
  ∂[ # c , c' ] with c ≟ c'
  ...| yes refl = ε
  ...| no prf = ∅
  ∂[ e ∙ e' , c ] with ν[ e ]
  ∂[ e ∙ e' , c ] | yes pr = (∂[ e , c ] `∙ e') `+ ∂[ e' , c ] 
  ∂[ e ∙ e' , c ] | no ¬pr = ∂[ e , c ] `∙ e'
  ∂[ e + e' , c ] = ∂[ e , c ] `+ ∂[ e' , c ]
  ∂[ e ⋆ , c ] = ∂[ e , c ] `∙ (e `⋆)

  ∂-sound : ∀ (x : Char)(xs : List Char)(e : Regex) →
            xs ∈[ ∂[ e , x ] ] →
            (x ∷ xs) ∈[ e ]
  ∂-sound x xs ∅ ()
  ∂-sound x xs ε ()
  ∂-sound x xs (# x₁) pr with x₁ ≟ x
  ∂-sound x .[] (# .x) ε | yes refl = # x
  ∂-sound x xs (# x₁) () | no ¬p
  ∂-sound x xs (e ∙ e₁) pr with ν[ e ]
  ∂-sound x xs (e ∙ e₁) pr | yes p with `+-sound (∂[ e , x ] `∙ e₁) (∂[ e₁ , x ]) {xs = xs} pr
  ∂-sound x xs (e ∙ e₁) pr | yes p | (.(∂[ e₁ , x ]) +L prf) with `∙-sound ∂[ e , x ] e₁ {xs = xs} prf
  ∂-sound x xs (e ∙ e₁) pr | yes p | (.(∂[ e₁ , x ]) +L prf) | (pr1 ∙ pr2 ⇒ refl) = ∂-sound x _  e pr1 ∙ pr2 ⇒ refl
  ∂-sound x xs (e ∙ e₁) pr | yes p | (.(∂[ e , x ] `∙ e₁) +R prf) = p ∙ ∂-sound x xs e₁ prf ⇒ refl
  ∂-sound x xs (e ∙ e₁) pr | no ¬p with `∙-sound ∂[ e , x ] e₁ pr
  ∂-sound x xs (e ∙ e₁) pr | no ¬p | (pr1 ∙ pr2 ⇒ refl) = ∂-sound x _ e pr1 ∙ pr2 ⇒ refl
  ∂-sound x xs (e + e₁) pr with `+-sound ∂[ e , x ] ∂[ e₁ , x ] pr
  ∂-sound x xs (e + e₁) pr | .(∂[ e₁ , x ]) +L prf = _ +L ∂-sound x xs e prf
  ∂-sound x xs (e + e₁) pr | .(∂[ e , x ]) +R prf = _ +R ∂-sound x xs e₁ prf
  ∂-sound x xs (e ⋆) pr with `∙-sound ∂[ e , x ] (e `⋆) pr
  ∂-sound x ._ (e ⋆) pr | prf ∙ prf1 ⇒ refl = (_ +R (∂-sound x _ e prf ∙ `⋆-sound e prf1 ⇒ refl)) ⋆

  ∂-complete : ∀ (x : Char)(xs : List Char)(e : Regex) →
               (x ∷ xs) ∈[ e ] → xs ∈[ ∂[ e , x ] ]
  ∂-complete x xs ∅ ()
  ∂-complete x xs ε ()
  ∂-complete x xs (# x₁) pr with x₁ ≟ x
  ∂-complete x .[] (# .x) (# .x) | yes refl = ε
  ∂-complete x .[] (# .x) (# .x) | no ¬p = ⊥-elim (¬p refl)
  ∂-complete x xs (e ∙ e₁) pr with ν[ e ]
  ∂-complete x xs (e ∙ e₁) (_∙_⇒_ {xs = []} pr pr₁ refl) | yes p
    = `+-complete (∂[ e , x ] `∙ e₁) ∂[ e₁ , x ] (_ +R ∂-complete x xs e₁ pr₁)
  ∂-complete x .(ys ++ _) (e ∙ e₁) (_∙_⇒_ {xs = .x ∷ ys} pr pr₁ refl) | yes p
    = `+-complete (∂[ e , x ] `∙ e₁) (∂[ e₁ , x ]) (_ +L (`∙-complete ∂[ e , x ] e₁ (∂-complete x _ e pr ∙ pr₁ ⇒ refl) ) )
  ∂-complete x xs (e ∙ e₁) (_∙_⇒_ {xs = []} {ys} pr pr1 eq) | no ¬p = ⊥-elim (¬p pr)
  ∂-complete x xs (e ∙ e₁) (_∙_⇒_ {xs = .x ∷ xs₁} {ys} pr pr1 refl) | no ¬p
    = `∙-complete ∂[ e , x ] e₁ (∂-complete x _ e pr ∙ pr1 ⇒ refl)
  ∂-complete x xs (e + e₁) (.e₁ +L pr) = `+-complete ∂[ e , x ] ∂[ e₁ , x ] (_ +L ∂-complete x xs e pr)
  ∂-complete x xs (e + e₁) (.e +R pr) = `+-complete ∂[ e , x ] ∂[ e₁ , x ] (_ +R ∂-complete x xs e₁ pr)
  ∂-complete x xs (e ⋆) ((.(e ∙ e ⋆) +L ()) ⋆)
  ∂-complete x xs (e ⋆) ((.ε +R _∙_⇒_ {xs = []} pr pr₁ refl) ⋆) = ∂-complete x xs (e ⋆) pr₁
  ∂-complete x xs (e ⋆) ((.ε +R _∙_⇒_ {xs = .x ∷ xs₁} pr pr₁ refl) ⋆)
    = `∙-complete ∂[ e , x ] (e `⋆) (∂-complete x _ _ pr ∙ `⋆-complete e pr₁ ⇒ refl)
