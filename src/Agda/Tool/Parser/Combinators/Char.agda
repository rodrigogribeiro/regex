open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Char
open import Data.List as List
open import Data.String using (String ; toList)
open import Data.Unit using (⊤ ; tt)

open import Function

open import Relation.Nullary
open import Relation.Nullary.Decidable

module Tool.Parser.Combinators.Char where
  open import Tool.Bindings.Primitives
  open import Tool.Parser.Combinators.Core

  private
    elem : Char → List Char → Bool
    elem c [] = false
    elem c (x ∷ xs) with c ≟ x
    ...| yes p = true
    ...| no p  = elem c xs

  char : Char → Parser Char
  char c = sat (⌊_⌋ ∘ _≟_ c)

  oneOf : String → Parser Char
  oneOf s = sat (λ c → elem c cs)
            where
              cs = toList s

  noneOf : String → Parser Char
  noneOf s = sat (λ c → not (elem c cs))
             where
               cs = toList s

  spaces : Parser ⊤
  spaces = tt <$ many (sat isSpace)


  lexeme : {A : Set} → Parser A → Parser A
  lexeme p = p <* spaces

  between : {A : Set} → Parser Char → Parser A → Parser Char → Parser A
  between l p r = l *> p <* r

  brackets : {A : Set} → Parser A → Parser A
  brackets p = between (char '[') p (char ']')

  parens : {A : Set} → Parser A → Parser A
  parens p = between (char '(') p (char ')')  
