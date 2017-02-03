open import Algebra
open import Data.Char
open import Data.List as List
open import Data.Product

open import Function

open import Relation.Binary.PropositionalEquality

open import Base.Regex
open import Base.EmptynessTest

module Derivative.Smart where

  -- smart constructors for regex quotienting

  infixr 5 _`+_

  _`+_ : (e e' : Regex) → Regex
  ∅ `+ e' = e'
  e `+ ∅  = e
  e `+ e' = e + e'

  `+-sound : ∀ (e e' : Regex){xs} →
               xs ∈[ e `+ e' ]    →
               xs ∈[ e + e'  ]
  `+-sound ∅ ∅ ()
  `+-sound ∅ ε ε = ∅ +R ε
  `+-sound ∅ (# x) (# .x) = ∅ +R (# x)
  `+-sound ∅ (e' ∙ e'') (pr ∙ pr1 ⇒ x) = ∅ +R pr ∙ pr1 ⇒ x
  `+-sound ∅ (e' + e'') (.e'' +L pr) = ∅ +R e'' +L pr
  `+-sound ∅ (e' + e'') (.e' +R pr) = ∅ +R e' +R pr
  `+-sound ∅ (e' ⋆) pr = ∅ +R pr
  `+-sound ε ∅ pr = ∅ +L pr
  `+-sound ε ε pr = pr
  `+-sound ε (# x) pr = pr
  `+-sound ε (e' ∙ e'') pr = pr
  `+-sound ε (e' + e'') pr = pr
  `+-sound ε (e' ⋆) pr = pr
  `+-sound (# x) ∅ pr = ∅ +L pr
  `+-sound (# x) ε pr = pr
  `+-sound (# x) (# x₁) pr = pr
  `+-sound (# x) (e' ∙ e'') pr = pr
  `+-sound (# x) (e' + e'') pr = pr
  `+-sound (# x) (e' ⋆) pr = pr
  `+-sound (e ∙ e₁) ∅ pr = ∅ +L pr
  `+-sound (e ∙ e₁) ε pr = pr
  `+-sound (e ∙ e₁) (# x) pr = pr
  `+-sound (e ∙ e₁) (e' ∙ e'') pr = pr
  `+-sound (e ∙ e₁) (e' + e'') pr = pr
  `+-sound (e ∙ e₁) (e' ⋆) pr = pr
  `+-sound (e + e₁) ∅ pr = ∅ +L pr
  `+-sound (e + e₁) ε pr = pr
  `+-sound (e + e₁) (# x) pr = pr
  `+-sound (e + e₁) (e' ∙ e'') pr = pr
  `+-sound (e + e₁) (e' + e'') pr = pr
  `+-sound (e + e₁) (e' ⋆) pr = pr
  `+-sound (e ⋆) ∅ pr = ∅ +L pr
  `+-sound (e ⋆) ε pr = pr
  `+-sound (e ⋆) (# x) pr = pr
  `+-sound (e ⋆) (e' ∙ e'') pr = pr
  `+-sound (e ⋆) (e' + e'') pr = pr
  `+-sound (e ⋆) (e' ⋆) pr = pr                 

  `+-complete : ∀ (e e' : Regex){xs} → xs ∈[ e + e' ] → xs ∈[ e `+ e' ]
  `+-complete ∅ ∅ (.∅ +L ())
  `+-complete ∅ ∅ (.∅ +R ()) 
  `+-complete ∅ ε (.ε +L ())
  `+-complete ∅ ε (.∅ +R pr) = pr
  `+-complete ∅ (# x) (.(# x) +L ())
  `+-complete ∅ (# x) (.∅ +R pr) = pr
  `+-complete ∅ (e' ∙ e'') (.(e' ∙ e'') +L ())
  `+-complete ∅ (e' ∙ e'') (.∅ +R pr) = pr
  `+-complete ∅ (e' + e'') (.(e' + e'') +L ())
  `+-complete ∅ (e' + e'') (.∅ +R pr) = pr
  `+-complete ∅ (e' ⋆) (.(e' ⋆) +L ())
  `+-complete ∅ (e' ⋆) (.∅ +R pr) = pr
  `+-complete ε ∅ (.∅ +L pr) = pr
  `+-complete ε ∅ (.ε +R ())
  `+-complete ε ε pr = pr
  `+-complete ε (# x) pr = pr
  `+-complete ε (e' ∙ e'') pr = pr
  `+-complete ε (e' + e'') pr = pr
  `+-complete ε (e' ⋆) pr = pr
  `+-complete (# x) ∅ (.∅ +L pr) = pr
  `+-complete (# x) ∅ (.(# x) +R ())
  `+-complete (# x) ε pr = pr
  `+-complete (# x) (# x₁) pr = pr
  `+-complete (# x) (e' ∙ e'') pr = pr
  `+-complete (# x) (e' + e'') pr = pr
  `+-complete (# x) (e' ⋆) pr = pr
  `+-complete (e ∙ e₁) ∅ (.∅ +L pr) = pr
  `+-complete (e ∙ e₁) ∅ (.(e ∙ e₁) +R ())
  `+-complete (e ∙ e₁) ε pr = pr
  `+-complete (e ∙ e₁) (# x) pr = pr
  `+-complete (e ∙ e₁) (e' ∙ e'') pr = pr
  `+-complete (e ∙ e₁) (e' + e'') pr = pr
  `+-complete (e ∙ e₁) (e' ⋆) pr = pr
  `+-complete (e + e₁) ∅ (.∅ +L pr) = pr
  `+-complete (e + e₁) ∅ (.(e + e₁) +R ())
  `+-complete (e + e₁) ε pr = pr
  `+-complete (e + e₁) (# x) pr = pr
  `+-complete (e + e₁) (e' ∙ e'') pr = pr
  `+-complete (e + e₁) (e' + e'') pr = pr
  `+-complete (e + e₁) (e' ⋆) pr = pr
  `+-complete (e ⋆) ∅ (.∅ +L pr) = pr
  `+-complete (e ⋆) ∅ (.(e ⋆) +R ())
  `+-complete (e ⋆) ε pr = pr
  `+-complete (e ⋆) (# x) pr = pr
  `+-complete (e ⋆) (e' ∙ e'') pr = pr
  `+-complete (e ⋆) (e' + e'') pr = pr
  `+-complete (e ⋆) (e' ⋆) pr = pr


  infixr 6 _`∙_

  _`∙_ : (e e' : Regex) -> Regex
  ∅ `∙ e' = ∅
  ε `∙ e' = e'
  e `∙ ∅ = ∅
  e `∙ ε = e
  e `∙ e' = e ∙ e'

  module LM = Monoid (List.monoid Char)

  `∙-sound : ∀ (e e' : Regex){xs} → xs ∈[ e `∙ e' ] → xs ∈[ e ∙ e' ]
  `∙-sound ∅ ∅ ()
  `∙-sound ∅ ε ()
  `∙-sound ∅ (# x) ()
  `∙-sound ∅ (e' ∙ e'') () 
  `∙-sound ∅ (e' + e'') ()
  `∙-sound ∅ (e' ⋆) ()
  `∙-sound ε ∅ ()
  `∙-sound ε ε pr = ε ∙ pr ⇒ refl
  `∙-sound ε (# x) pr = ε ∙ pr ⇒ refl
  `∙-sound ε (e' ∙ e'') pr = ε ∙ pr ⇒ refl
  `∙-sound ε (e' + e'') pr = ε ∙ pr ⇒ refl
  `∙-sound ε (e' ⋆) pr = ε ∙ pr ⇒ refl
  `∙-sound (# x) ∅ ()
  `∙-sound (# x) ε pr = pr ∙ ε ⇒ (sym $ proj₂ LM.identity _)
  `∙-sound (# x) (# x₁) pr = pr
  `∙-sound (# x) (e' ∙ e'') pr = pr
  `∙-sound (# x) (e' + e'') pr = pr
  `∙-sound (# x) (e' ⋆) pr = pr
  `∙-sound (e ∙ e₁) ∅ ()
  `∙-sound (e ∙ e₁) ε pr = pr ∙ ε ⇒ (sym $ proj₂ LM.identity _)
  `∙-sound (e ∙ e₁) (# x) pr = pr
  `∙-sound (e ∙ e₁) (e' ∙ e'') pr = pr
  `∙-sound (e ∙ e₁) (e' + e'') pr = pr
  `∙-sound (e ∙ e₁) (e' ⋆) pr = pr
  `∙-sound (e + e₁) ∅ ()
  `∙-sound (e + e₁) ε pr = pr ∙ ε ⇒ (sym $ proj₂ LM.identity _)
  `∙-sound (e + e₁) (# x) pr = pr
  `∙-sound (e + e₁) (e' ∙ e'') pr = pr
  `∙-sound (e + e₁) (e' + e'') pr = pr
  `∙-sound (e + e₁) (e' ⋆) pr = pr
  `∙-sound (e ⋆) ∅ ()
  `∙-sound (e ⋆) ε pr = pr ∙ ε ⇒ (sym $ proj₂ LM.identity _)
  `∙-sound (e ⋆) (# x) pr = pr
  `∙-sound (e ⋆) (e' ∙ e'') pr = pr
  `∙-sound (e ⋆) (e' + e'') pr = pr
  `∙-sound (e ⋆) (e' ⋆) pr = pr

  `∙-complete : ∀ (e e' : Regex){xs} → xs ∈[ e ∙ e' ] → xs ∈[ e `∙ e' ]
  `∙-complete ∅ ∅ (() ∙ pr1 ⇒ eq)
  `∙-complete ∅ ε (() ∙ pr1 ⇒ x) 
  `∙-complete ∅ (# x) (() ∙ pr1 ⇒ x1)
  `∙-complete ∅ (e' ∙ e'') (() ∙ pr1 ⇒ x)
  `∙-complete ∅ (e' + e'') (() ∙ pr1 ⇒ x)
  `∙-complete ∅ (e' ⋆) (() ∙ pr₁ ⇒ x)
  `∙-complete ε ∅ (pr ∙ () ⇒ x)
  `∙-complete ε ε (ε ∙ ε ⇒ refl) = ε
  `∙-complete ε (# x) (ε ∙ pr₁ ⇒ refl) = pr₁
  `∙-complete ε (e' ∙ e'') (ε ∙ pr₁ ⇒ refl) = pr₁
  `∙-complete ε (e' + e'') (ε ∙ pr₁ ⇒ refl) = pr₁
  `∙-complete ε (e' ⋆) (ε ∙ pr₁ ⇒ refl) = pr₁
  `∙-complete (# x) ∅ (pr ∙ () ⇒ x₁)
  `∙-complete (# x) ε ((# .x) ∙ ε ⇒ refl) = # x
  `∙-complete (# x) (# x₁) pr = pr
  `∙-complete (# x) (e' ∙ e'') pr = pr
  `∙-complete (# x) (e' + e'') pr = pr
  `∙-complete (# x) (e' ⋆) pr = pr
  `∙-complete (e ∙ e₁) ∅ (pr ∙ () ⇒ x)
  `∙-complete (e ∙ e₁) ε (_∙_⇒_ {xs = xs} pr ε refl) rewrite proj₂ LM.identity xs = pr
  `∙-complete (e ∙ e₁) (# x) pr = pr
  `∙-complete (e ∙ e₁) (e' ∙ e'') pr = pr
  `∙-complete (e ∙ e₁) (e' + e'') pr = pr
  `∙-complete (e ∙ e₁) (e' ⋆) pr = pr
  `∙-complete (e + e₁) ∅ (pr ∙ () ⇒ x)
  `∙-complete (e + e₁) ε (_∙_⇒_ {xs = xs} (.e₁ +L pr) ε refl) rewrite proj₂ LM.identity xs = e₁ +L pr
  `∙-complete (e + e₁) ε (_∙_⇒_ {xs = xs} (.e +R pr) ε refl) rewrite proj₂ LM.identity xs = e +R pr
  `∙-complete (e + e₁) (# x) pr = pr
  `∙-complete (e + e₁) (e' ∙ e'') pr = pr
  `∙-complete (e + e₁) (e' + e'') pr = pr
  `∙-complete (e + e₁) (e' ⋆) pr = pr
  `∙-complete (e ⋆) ∅ (pr ∙ () ⇒ x)
  `∙-complete (e ⋆) ε (_∙_⇒_ {xs = xs} pr ε refl ) rewrite proj₂ LM.identity xs = pr
  `∙-complete (e ⋆) (# x) pr = pr
  `∙-complete (e ⋆) (e' ∙ e'') pr = pr
  `∙-complete (e ⋆) (e' + e'') pr = pr
  `∙-complete (e ⋆) (e' ⋆) pr = pr


  infix 7 _`⋆

  _`⋆ : Regex → Regex
  ∅ `⋆ = ε
  ε `⋆ = ε
  e `⋆ = e ⋆


  `⋆-sound : ∀ (e : Regex){xs} → xs ∈[ e `⋆ ] → xs ∈[ e ⋆ ]
  `⋆-sound ∅ ε = (_ +L ε) ⋆
  `⋆-sound ε pr = (_ +L pr) ⋆
  `⋆-sound (# x) pr = pr
  `⋆-sound (e ∙ e₁) pr = pr
  `⋆-sound (e + e₁) pr = pr
  `⋆-sound (e ⋆) pr = pr


  `⋆-complete : ∀ (e : Regex){xs} → xs ∈[ e ⋆ ] → xs ∈[ e `⋆ ]
  `⋆-complete ∅ ((_ +L pr) ⋆) = pr
  `⋆-complete ∅ ((_ +R () ∙ pr₁ ⇒ x) ⋆)
  `⋆-complete ε ((_ +L pr) ⋆) = pr
  `⋆-complete ε ((.ε +R ε ∙ pr₁ ⇒ refl) ⋆) = `⋆-complete ε pr₁
  `⋆-complete (# x) pr = pr
  `⋆-complete (e ∙ e₁) pr = pr
  `⋆-complete (e + e₁) pr = pr
  `⋆-complete (e ⋆) pr = pr
