open import Data.Bool renaming (_≟_ to _≡?_)
open import Data.Char
open import Data.List    hiding (any)
open import Data.Product hiding (map)

open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module Tool.Parser.Combinators.Core where

  -- type of parsers

  Input = List Char

  Parser : Set → Set
  Parser A = Input → List (A × Input)


  symbol : Char → Parser Char
  symbol c [] = []
  symbol c (x ∷ inp) with x ≟ c
  symbol c (.c ∷ inp) | yes refl = [ c , inp ]
  symbol c (x ∷ inp) | no ¬p =  []

  succeed : {A : Set} → A → Parser A
  succeed x = λ inp → [ x , inp ]

  fail : {A : Set} → Parser A
  fail = const []

  infixl 3 _<|>_

  _<|>_ : {A : Set} → Parser A → Parser A → Parser A
  p <|> p' = λ inp → p inp ++ p' inp

  infixl 4 _<*>_
  infixl 5 _<*_ _*>_

  _<*>_ : {A B : Set} → Parser (B → A) → Parser B → Parser A
  p <*> p' = λ inp → concatMap (λ f →
                         map (λ g →
                                ( (proj₁ f) (proj₁ g))
                                , (proj₂ g))
                             (p' (proj₂ f)))
                         (p inp)
  infix 7 _<$>_ _<$_ 

  _<$>_ : {A B : Set} → (A → B) → Parser A → Parser B
  f <$> p = succeed f <*> p

  _<$_ : {A B : Set} → A → Parser B → Parser A
  f <$ p = const f <$> p  

  _<*_ : {A B : Set} → Parser A → Parser B → Parser A
  p <* p' = const <$> p <*> p'

  _*>_ : {A B : Set} → Parser A → Parser B → Parser B
  p *> p' = flip const <$> p <*> p'

  choice : {A : Set} → List (Parser A) → Parser A
  choice = foldr _<|>_ fail

  {-# TERMINATING #-}

  many : {A : Set} → Parser A → Parser (List A)
  many p = (_∷_) <$> p <*> (many p) <|> succeed []

  sat : (Char → Bool) → Parser Char
  sat p [] = []
  sat p (x ∷ xs) with p x
  sat p (x ∷ xs) | false = []
  sat p (x ∷ xs) | true = [ x , xs ]

  any : Parser Char
  any = sat (const true)

  some : {A : Set} → Parser A → Parser (List A)
  some p = _∷_ <$> p <*> many p 
  
