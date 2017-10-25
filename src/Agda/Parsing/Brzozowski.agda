open import Data.Char
open import Data.List

open import Function

open import Relation.Nullary

open import Base.Regex
open import Base.EmptynessTest
open import Derivative.Brzozowski

module Parsing.Brzozowski where

  -- simple parsing algorithm using Brzozowski derivatives.

  parse : ∀ (e : Regex)(xs : List Char) → Dec (xs ∈[ e ])
  parse e [] = ν[ e ]
  parse e (x ∷ xs) with parse (∂[ e , x ]) xs
  parse e (x ∷ xs) | yes p = yes (∂-sound x xs e p)
  parse e (x ∷ xs) | no ¬p = no (¬p ∘ ∂-complete x xs e )
