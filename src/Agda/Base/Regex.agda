open import Algebra

open import Data.Char
open import Data.List renaming ([_] to [[_]])
open import Data.List.Properties
open import Data.Product 
open import Data.String renaming (_++_ to _++s_)
open import Data.Sum

open import Function

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary


module Base.Regex where

  -- definition of a regular expression data type

  infixr 5 _+_
  infixr 6 _∙_
  infixl 7 _⋆

  data Regex : Set where
    ∅  : Regex
    ε   : Regex
    #_  : Char → Regex
    _∙_ : Regex → Regex → Regex
    _+_ : Regex → Regex → Regex
    _⋆  : Regex → Regex


  -- semantics for regex

  infix 3 _∈[_]
  infixr 5 _+L_ _+R_
  infixr 6 _∙_⇒_

  data _∈[_] : List Char → Regex → Set where
    ε  : [] ∈[ ε ]
    #_ : ∀ (c : Char) → [[ c ]] ∈[ # c ]
    _∙_⇒_ : ∀ {l r xs ys zs} →
              xs ∈[ l ]      →
              ys ∈[ r ]      →
              zs ≡ xs ++ ys  →
              zs ∈[ l ∙ r ]
    _+L_ : ∀ {l xs}(r : Regex) →
           xs ∈[ l ]           →
           xs ∈[ l + r ] 
    _+R_ : ∀ {r xs}(l : Regex) →
           xs ∈[ r ]           →
           xs ∈[ l + r ]
    _⋆   : ∀ {xs l} →
           xs ∈[ ε + (l ∙ l ⋆)] →
           xs ∈[ l ⋆ ]
    
  -- some inversion lemmas for semantics

  ∈+-invert : ∀ {xs l r} → xs ∈[ l + r ] → xs ∈[ l ] ⊎ xs ∈[ r ]
  ∈+-invert (r +L pr) = inj₁ pr
  ∈+-invert (l +R pr) = inj₂ pr


  []∈∙-invert : ∀ {l r} → [] ∈[ l ∙ r ] → [] ∈[ l ] × [] ∈[ r ]
  []∈∙-invert (_∙_⇒_ {xs = []} pr pr' refl) = pr , pr'
  []∈∙-invert (_∙_⇒_ {xs = x ∷ xs} pr pr' ())

  ∅∈-invert : ∀ {xs} → ¬ (xs ∈[ ∅ ])
  ∅∈-invert ()

  #-∈-invert : ∀ {x y xs} → x ∷ xs ∈[ # y ] → x ≡ y × xs ≡ []
  #-∈-invert (# c) = refl , refl

  -- more lemmas

  ∙-dist-+-right : ∀ {e e1 e' s} → s ∈[ e ∙ e' ] → s ∈[ (e + e1) ∙ e' ]
  ∙-dist-+-right (pr ∙ pr₁ ⇒ x) = (_ +L pr) ∙ pr₁ ⇒ x 

  ∙-dist-+-left : ∀ {e e1 e' s} → s ∈[ e1 ∙ e' ] → s ∈[ (e + e1) ∙ e' ]
  ∙-dist-+-left (pr ∙ pr₁ ⇒ x) = (_ +R pr) ∙ pr₁ ⇒ x 

  ∙-assocl : ∀ {e e' e'' s} → s ∈[ (e ∙ e') ∙ e'' ] → s ∈[ e ∙ (e' ∙ e'') ]
  ∙-assocl (_∙_⇒_ {ys = zs}(_∙_⇒_ {xs = xs}{ys = ys} pr pr₁ refl) pr₂ refl)
    = pr ∙ (pr₁ ∙ pr₂ ⇒ refl) ⇒ LM.assoc xs ys zs
      where
        module LM = Monoid (Data.List.monoid Char)

  ∙-assocr : ∀ {e e' e'' s} → s ∈[ e ∙ (e' ∙ e'') ] → s ∈[ (e ∙ e') ∙ e'' ]
  ∙-assocr (_∙_⇒_ {xs = zs} pr (_∙_⇒_ {xs = xs}{ys = ys} pr1 pr2 refl) refl)
    = (pr ∙ pr1 ⇒ refl) ∙ pr2 ⇒ (sym $ LM.assoc zs xs ys)
      where
        module LM = Monoid (Data.List.monoid Char)
  

  open import Relation.Binary

  #-inv : ∀ {c c' : Char} → (Regex.# c) ≡ (# c') → c ≡ c'
  #-inv refl = refl

  ∙-inv : ∀ {e e' e1 e1'} → (e ∙ e') ≡ (e1 ∙ e1') → (e ≡ e1) × (e' ≡ e1')
  ∙-inv refl = refl , refl

  +-inv : ∀ {e e' e1 e1'} → (e + e') ≡ (e1 + e1') → (e ≡ e1) × (e' ≡ e1')
  +-inv refl = refl , refl

  ⋆-inv : ∀ {e e'} → (Regex._⋆ e) ≡ (Regex._⋆ e') → (e ≡ e')
  ⋆-inv refl = refl

  _≡?_ : Decidable {A = Regex} _≡_
  ∅ ≡? ∅ = yes refl
  ∅ ≡? ε = no (λ ())
  ∅ ≡? (# x) = no (λ ())
  ∅ ≡? (e' ∙ e'') = no (λ ())
  ∅ ≡? (e' + e'') = no (λ ())
  ∅ ≡? (e' ⋆) = no (λ ())
  ε ≡? ∅ = no (λ ())
  ε ≡? ε = yes refl
  ε ≡? (# x) = no (λ ())
  ε ≡? (e' ∙ e'') = no (λ ())
  ε ≡? (e' + e'') = no (λ ())
  ε ≡? (e' ⋆) = no (λ ())
  (# x) ≡? ∅ = no (λ ())
  (# x) ≡? ε = no (λ ())
  (# x) ≡? (# x₁) with x Data.Char.≟ x₁
  (# x) ≡? (# .x) | yes refl = yes refl
  (# x) ≡? (# x₁) | no ¬p = no (¬p ∘ #-inv)
  (# x) ≡? (e' ∙ e'') = no (λ ())
  (# x) ≡? (e' + e'') = no (λ ())
  (# x) ≡? (e' ⋆) = no (λ ())
  (e ∙ e₁) ≡? ∅ = no (λ ())
  (e ∙ e₁) ≡? ε = no (λ ())
  (e ∙ e₁) ≡? (# x) = no (λ ())
  (e ∙ e₁) ≡? (e' ∙ e'') with e ≡? e' | e₁ ≡? e''
  (e ∙ e₁) ≡? (.e ∙ .e₁) | yes refl | (yes refl) = yes refl
  (e ∙ e₁) ≡? (e' ∙ e'') | yes p | (no ¬p) = no (¬p ∘ proj₂ ∘ ∙-inv)
  (e ∙ e₁) ≡? (e' ∙ e'') | no ¬p | q = no (¬p ∘ proj₁ ∘ ∙-inv)
  (e ∙ e₁) ≡? (e' + e'') = no (λ ())
  (e ∙ e₁) ≡? (e' ⋆) = no (λ ())
  (e + e₁) ≡? ∅ = no (λ ())
  (e + e₁) ≡? ε = no (λ ())
  (e + e₁) ≡? (# x) = no (λ ())
  (e + e₁) ≡? (e' ∙ e'') = no (λ ())
  (e + e₁) ≡? (e' + e'') with e ≡? e' | e₁ ≡? e''
  (e + e₁) ≡? (.e + .e₁) | yes refl | (yes refl) = yes refl
  (e + e₁) ≡? (e' + e'') | yes p | (no ¬p) = no (¬p ∘ proj₂ ∘ +-inv)
  (e + e₁) ≡? (e' + e'') | no ¬p | q = no (¬p ∘ proj₁ ∘ +-inv)
  (e + e₁) ≡? (e' ⋆) = no (λ ())
  (e ⋆) ≡? ∅ = no (λ ())
  (e ⋆) ≡? ε = no (λ ())
  (e ⋆) ≡? (# x) = no (λ ())
  (e ⋆) ≡? (e' ∙ e'') = no (λ ())
  (e ⋆) ≡? (e' + e'') = no (λ ())
  (e ⋆) ≡? (e' ⋆) with e ≡? e'
  (e ⋆) ≡? (.e ⋆) | yes refl = yes refl
  (e ⋆) ≡? (e' ⋆) | no ¬p = no (¬p ∘ ⋆-inv)
