open import Data.List

open import Function

module Tool.Parser.RegexParser where
  open import Tool.Parser.Combinators
  open import Base.Regex

  pChar : Parser Regex
  pChar = #_ <$> noneOf "[]()*+"

  pAtom : Parser Regex
  pAtom = foldl _∙_ ε <$> some pChar

  pstar : Parser (Regex → Regex)
  pstar = const _⋆ <$> lexeme (char '*')

  pPlus : Parser (Regex → Regex)
  pPlus = const (\e → e ∙ (e ⋆)) <$> lexeme (char '+')

  pInBracketsChar : Parser Regex
  pInBracketsChar = #_ <$> noneOf "[]^"

  pBrackets : Parser Regex
  pBrackets = foldl _+_ ∅ <$> (brackets (many pInBracketsChar))

  pStar : Parser (Regex → Regex)
  pStar = pstar <|> succeed id

  {-# TERMINATING #-}

  mutual
    pFactor : Parser Regex
    pFactor =  pBrackets <|> pAtom <|> (parens pExp)

    pTerm : Parser Regex
    pTerm = f <$> pFactor <*> (pPlus <|> pStar)
            where
              f : {A B : Set} → A → (A → B) → B
              f e g = g e

    pExp : Parser Regex
    pExp = foldl _∙_ ε <$> many pTerm
