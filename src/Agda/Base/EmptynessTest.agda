open import Data.List
open import Data.Product using (proj₁ ; proj₂)
open import Data.Sum

open import Function

open import Base.Regex
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Base.EmptynessTest where

  -- certified emptyness test

  ν[_] : ∀ (e : Regex) → Dec ( [] ∈[ e ])
  ν[ ∅ ] = no (λ ())
  ν[ ε ] = yes ε
  ν[ # x ] = no (λ ())
  ν[ e ∙ e' ] with ν[ e ] | ν[ e' ]
  ν[ e ∙ e' ] | yes pr | (yes pr1) = yes (pr ∙ pr1 ⇒ refl)
  ν[ e ∙ e' ] | yes pr | (no ¬pr1) = no (¬pr1 ∘ proj₂ ∘ []∈∙-invert)
  ν[ e ∙ e' ] | no ¬pr | pr1 = no (¬pr ∘ proj₁ ∘ []∈∙-invert)
  ν[ e + e' ] with ν[ e ] | ν[ e' ]
  ν[ e + e' ] | yes pr | pr1 = yes (e' +L pr)
  ν[ e + e' ] | no ¬pr | (yes pr1) = yes (e +R pr1)
  ν[ e + e' ] | no ¬pr | (no ¬pr1) = no ( [ ¬pr , ¬pr1 ] ∘ ∈+-invert)
  ν[ e ⋆ ] = yes ((e ∙ e ⋆ +L ε) ⋆) 
