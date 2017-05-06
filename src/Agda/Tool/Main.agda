open import Coinduction

open import Data.Bool
open import Data.Char    as Chr
open import Data.Colist  as Colist 
open import Data.List    as List
open import Data.Maybe   as Maybe
open import Data.Product
open import Data.String  as Str
open import Data.Unit

open import Function

open import IO as IO

open import Relation.Nullary
open import Relation.Nullary.Decidable

module Tool.Main where

  open import Base.Regex
  open import BitCoded.BitRegex

  open import Substring.SubstringDef
  open import Substring.SubstringAntimirov as Ant
  open import Substring.SubstringBrzozowski as Br
  open import Substring.BitSubstring as Bt

  open import Tool.Bindings.Arguments
  open import Tool.Parser.Arguments.Options
  open import Tool.Parser.RegexParser

  usage : String
  usage = "Usage: verigrep [OPTIONS] [REGEXP] [FILELIST]" Str.++
          "\n\nwhere\nOPTIONS\n-B: parse with Brzozowski derivatives\n" Str.++
          "-A: parse with Antimirov derivatives\n" Str.++
          "-C: parse with Bit codes derivatives\n" Str.++
          "-v: Show version information" Str.++
          "-h: help message"

  versionInfo : String
  versionInfo = "verigrep - version 0.1"


  breakOn : {A : Set} (P? : A → Bool) (xs : List A) → List (List A)
  breakOn {A} P? = uncurry _∷_ ∘ foldr step ([] , [])
    where
      step : A → (List A × List (List A)) → (List A × List (List A))
      step a (xs , xss) = if (P? a) then [] , xs ∷ xss else a ∷ xs , xss

  lines : String → List String
  lines = List.map Str.fromList ∘ breakOn isNewLine ∘ Str.toList
    where
      isNewLine : Char → Bool
      isNewLine y =  ⌊ (y Chr.≟ '\n') ⌋ 


  choose : Options → (e : Regex) → (xs : List Char) → Dec (IsSubstring xs e)
  choose opt e with algorithm opt
  ...| Antimirov  = flip Ant.IsSubstringDec e
  ...| Brzozowski = flip Br.IsSubstringDec e
  ...| BitCodes   = flip Bt.IsSubstringDec e

  showResult : ∀ {xs e} → IsSubstring xs e → IO ⊤
  showResult (Substring ys zs ws _ _)
    = putStrLn ("\nLine:" Str.++ xs' Str.++ " matches: " Str.++ zs')
      where
         xs' = Str.fromList (ys List.++ zs List.++ ws)
         zs' = Str.fromList zs

  result : ∀ {xs e} → Dec (IsSubstring xs e) → IO ⊤
  result (yes pr) = showResult pr
  result (no _)   = return tt

  verigrep : Options → Regex → List String → IO ⊤
  verigrep opt r [] = return tt
  verigrep opt r (f ∷ fs)
    = ♯  IO.readFiniteFile f          >>= λ c → 
         ♯ (♯ (IO.mapM′ (result ∘ choose opt r ∘ Str.toList)
                 $ Colist.fromList (lines c))
            >> (♯ verigrep opt r fs))

  main : _
  main = IO.run $
           ♯ getArgs
           >>= λ args →
              ♯ let opt = parseOptions args in
                  if version opt
                  then putStrLn versionInfo
                  else if help opt
                       then putStrLn usage
                       else case Maybe.map (pExp ∘ toList) (regex opt) of λ{
                                 nothing                 → putStrLn usage
                              ;  (just [])               → putStrLn usage 
                              ;  (just (( e , _) ∷ _))   → verigrep opt e (files opt)
                              }   
                       
           
             
