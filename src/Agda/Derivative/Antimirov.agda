open import Agda.Primitive

open import Algebra

open import Data.Char
open import Data.Empty
open import Data.List
open import Data.List.Any
open import Data.List.Properties
open import Data.Product                          hiding (map)
open import Data.Sum                              hiding (map)

open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Derivative.Antimirov where
  open import Base.EmptynessTest
  open import Base.Regex
  module LM = Monoid (Data.List.monoid Regex)
  open Membership-≡ public


  Regexes = List Regex

  _⊚ᵣ_ : Regex → Regexes → Regexes
  e ⊚ᵣ [] = []
  e ⊚ᵣ (e' ∷ es) = (e' ∙ e) ∷ (e ⊚ᵣ es)

  ∇[_,_] : Regex → Char → Regexes
  ∇[ ∅ , c ] = []
  ∇[ ε , c ] = []
  ∇[ # x , c ] with x ≟ c
  ∇[ # x , .x ] | yes refl = [ ε ]
  ∇[ # x , c ] | no ¬p = []
  ∇[ e ∙ e' , c ] with ν[ e ]
  ∇[ e ∙ e' , c ] | yes p = (e' ⊚ᵣ ∇[ e , c ]) ++ ∇[ e' , c ]
  ∇[ e ∙ e' , c ] | no ¬p = e' ⊚ᵣ ∇[ e , c ]
  ∇[ e + e' , c ] = ∇[ e , c ] ++ ∇[ e' , c ]
  ∇[ e ⋆ , c ] = (e ⋆) ⊚ᵣ ∇[ e , c ]

  infix 1 _∈⟨_⟩

  data _∈⟨_⟩ : List Char → Regexes → Set where
    Here  : ∀ {s e es} → s ∈[ e ] → s ∈⟨ e ∷ es ⟩
    There : ∀ {s e es} → s ∈⟨ es ⟩ → s ∈⟨ e ∷ es ⟩

  ∈-++ : ∀ {s es es'} → s ∈⟨ es ++ es' ⟩ → (s ∈⟨ es ⟩) ⊎ (s ∈⟨ es' ⟩)
  ∈-++ {es = []} {[]} ()
  ∈-++ {es = []} {x ∷ es'} pr = inj₂ pr
  ∈-++ {es = x ∷ es} {[]} pr rewrite (proj₂ LM.identity (x ∷ es)) = inj₁ pr
  ∈-++ {es = x ∷ es} {x₁ ∷ es'} (Here pr) = inj₁ (Here pr)
  ∈-++ {es = x ∷ es} {x₁ ∷ es'} (There pr) with ∈-++ {es = es} {es' = x₁ ∷ es'} pr
  ∈-++ {_} {x₂ ∷ es} {x₁ ∷ es'} (There pr) | inj₁ x = inj₁ (There x)
  ∈-++ {_} {x ∷ es} {x₁ ∷ es'} (There pr) | inj₂ y = inj₂ y

  weak-∈-left : ∀ {s es} es' → s ∈⟨ es ⟩ → s ∈⟨ es ++ es' ⟩
  weak-∈-left es' (Here x) = Here x
  weak-∈-left es' (There pr) = There (weak-∈-left _ pr)

  weak-∈-right : ∀ {s es'} es → s ∈⟨ es' ⟩ → s ∈⟨ es ++ es' ⟩
  weak-∈-right [] (Here x) = Here x
  weak-∈-right (x ∷ []) (Here y) = There (Here y)
  weak-∈-right (x ∷ x₁ ∷ es₁) (Here x₂) = There (There (weak-∈-right es₁ (Here x₂)))
  weak-∈-right [] (There pr) = There pr
  weak-∈-right (x ∷ es₁) (There pr) = There (weak-∈-right es₁ (There pr))

  ⊚ᵣ-compose : ∀ {xs ys e es} → xs ∈⟨ es ⟩ → ys ∈[ e ] → xs ++ ys ∈⟨ e ⊚ᵣ es ⟩
  ⊚ᵣ-compose {e = e} {[]} () pr1
  ⊚ᵣ-compose {e = e} {x ∷ es} (Here pr) pr1 = Here (pr ∙ pr1 ⇒ refl)
  ⊚ᵣ-compose {e = e} {x ∷ es} (There pr) pr1 = There (⊚ᵣ-compose pr pr1)


  ⊚ᵣ-split : ∀ {s e es} → s ∈⟨ e ⊚ᵣ es ⟩ → ∃₂ (λ s1 s2 → (s ≡ s1 ++ s2) × (s1 ∈⟨ es ⟩) × s2 ∈[ e ])
  ⊚ᵣ-split {es = []} ()
  ⊚ᵣ-split {es = x ∷ es} (Here (pr ∙ pr₁ ⇒ x₁)) = _ , _ , x₁ , Here pr , pr₁
  ⊚ᵣ-split {es = x ∷ es} (There pr) with ⊚ᵣ-split pr
  ⊚ᵣ-split {_} {_} {x ∷ es} (There pr) | s1 , s2 , eq , pr1 , pr2 = s1 , s2 , eq , There pr1 , pr2

  ∇-sound : ∀ {s a} e → s ∈⟨ ∇[ e , a ] ⟩ → (a ∷ s) ∈[ e ]
  ∇-sound ∅ ()
  ∇-sound ε ()
  ∇-sound {a = a}(# x) pr with x ≟ a
  ∇-sound {_} {.x} (# x) (Here ε) | yes refl = # x
  ∇-sound {_} {.x} (# x) (There ()) | yes refl
  ∇-sound {_} {a} (# x) () | no ¬p
  ∇-sound (e ∙ e') pr with ν[ e ]
  ∇-sound {a = a}(e ∙ e') pr | yes p with ∈-++ {es = e' ⊚ᵣ ∇[ e , a ]}{es' = ∇[ e' , a ]} pr
  ∇-sound (e ∙ e') pr | yes p | (inj₁ x) with ⊚ᵣ-split x
  ∇-sound (e ∙ e') pr | yes p | (inj₁ x) | (s1 , s2 , refl , pr1 , pr2) = (∇-sound _ pr1) ∙ pr2 ⇒ refl
  ∇-sound (e ∙ e') pr | yes p | (inj₂ y) = p ∙ ∇-sound _ y ⇒ refl
  ∇-sound (e ∙ e') pr | no ¬p with ⊚ᵣ-split pr
  ∇-sound (e ∙ e') pr | no ¬p | s1 , s2 , refl , pr1 , pr2 = (∇-sound _ pr1) ∙ pr2 ⇒ refl
  ∇-sound {a = a}(e + e') pr with ∈-++ {es = ∇[ e , a ]}{es' = ∇[ e' , a ]} pr
  ∇-sound {_} {a} (e + e') pr | inj₁ x = _ +L ∇-sound _ x
  ∇-sound {_} {a} (e + e') pr | inj₂ y = _ +R ∇-sound _ y
  ∇-sound (e ⋆) pr with ⊚ᵣ-split pr
  ∇-sound (e ⋆) pr | s1 , s2 , refl , pr1 , pr2 = (_ +R (∇-sound _ pr1) ∙ pr2 ⇒ refl) ⋆


  ∇-complete : ∀ {s a} e → (a ∷ s) ∈[ e ] → s ∈⟨ ∇[ e , a ] ⟩
  ∇-complete ∅ ()
  ∇-complete ε ()
  ∇-complete {a = a}(# x) pr with x ≟ a
  ∇-complete {_} {.x} (# x) (# .x) | yes refl = Here ε
  ∇-complete {_} {.x} (# x) (# .x) | no ¬p = ⊥-elim (¬p refl)
  ∇-complete (e ∙ e₁) pr with ν[ e ]
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = []} {.(_ ∷ _)} pr pr1 refl) | yes p with ∇-complete _ pr1
  ∇-complete {a = a}(e ∙ e₁) (_∙_⇒_ {xs = []} {.(_ ∷ _)} pr pr1 refl) | yes p | k = weak-∈-right (e₁ ⊚ᵣ ∇[ e , a ]) k
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = x ∷ xs} {ys} pr pr1 refl) | yes p with ∇-complete e pr
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = x ∷ xs} {ys} pr pr1 refl) | yes p | pr' = weak-∈-left {es = e₁ ⊚ᵣ ∇[ e , x ]}∇[ e₁ , x ] (⊚ᵣ-compose pr' pr1) 
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = []} {.(_ ∷ _)} pr pr1 refl) | no ¬p = ⊥-elim (¬p pr)
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = x ∷ xs} {ys} pr pr1 refl) | no ¬p with ∇-complete e pr
  ∇-complete (e ∙ e₁) (_∙_⇒_ {xs = x ∷ xs} {ys} pr pr1 refl) | no ¬p | pr' = ⊚ᵣ-compose pr' pr1
  ∇-complete {a = a}(e + e₁) (.e₁ +L pr) = weak-∈-left ∇[ e₁ , a ] (∇-complete e pr)
  ∇-complete {a = a}(e + e₁) (.e +R pr) = weak-∈-right ∇[ e , a ] (∇-complete e₁ pr)
  ∇-complete (e ⋆) ((.(e ∙ e ⋆) +L ()) ⋆)
  ∇-complete (e ⋆) ((.ε +R _∙_⇒_ {xs = []} pr pr1 refl) ⋆) = ∇-complete _ pr1
  ∇-complete (e ⋆) ((.ε +R _∙_⇒_ {xs = x ∷ xs} pr pr1 refl) ⋆) = ⊚ᵣ-compose (∇-complete e pr) pr1
