open import Algebra 
open import Algebra.Structures 

open import Data.Char renaming (_≟_ to _≟C_)
open import Data.Empty
open import Data.List
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat renaming (_+_ to _+N_ ; _*_ to _*N_ ; erase to eraseN)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)

open import Function

open import Relation.Binary hiding (NonEmpty)
open import Relation.Binary.PropositionalEquality as PEq renaming ([_] to [[_]])
open import Relation.Nullary

open import Base.Regex
open import BitCoded.Recursion

module BitCoded.ParseTree where

  module BitDefs where
  
    data Bit : Set where
      0# 1# : Bit
      
    _≟B_ : Decidable {A = Bit} _≡_
    0# ≟B 0# = yes refl
    0# ≟B 1# = no (λ ())
    1# ≟B 0# = no (λ ())
    1# ≟B 1# = yes refl

    data _IsBitCodeOf_ : List Bit → Regex → Set where
      ε : [] IsBitCodeOf ε
      #_ : ∀ c → [] IsBitCodeOf (# c)
      inl : ∀ {l xs} r → xs IsBitCodeOf l → (0# ∷ xs) IsBitCodeOf (l + r)
      inr : ∀ {r xs} l → xs IsBitCodeOf r → (1# ∷ xs) IsBitCodeOf (l + r)
      _*_=>_ : ∀ {l r xs ys zs} → xs IsBitCodeOf l →
                                  ys IsBitCodeOf r →
                                  zs ≡ xs ++ ys →
                                  zs IsBitCodeOf (l ∙ r)
      star[] : ∀ {l} → [ 1# ] IsBitCodeOf (l ⋆)
      star-∷ : ∀ {l xs xss ys} → xs IsBitCodeOf l →
                                 xss IsBitCodeOf (l ⋆) →
                                 ys ≡ 0# ∷ xs ++ xss →
                                 ys IsBitCodeOf (l ⋆)
                                 
  open BitDefs


  data Tree : Regex → Set where
    ε : Tree ε
    #_ : (c : Char) → Tree (# c)
    inl : ∀ {l}(r : Regex)(tl : Tree l) → Tree (l + r)
    inr : ∀ {r}(l : Regex)(tr : Tree r) → Tree (l + r)
    _*_ : ∀ {l r}(tl : Tree l)(tr : Tree r) → Tree (l ∙ r)
    star[] : ∀ {l} → Tree (l ⋆)
    star-∷ : ∀ {l} → Tree l → Tree (l ⋆) → Tree (l ⋆)


  flat : ∀ {e} → Tree e → ∃ (λ xs → xs ∈[ e ])
  flat ε = [] , ε
  flat (# c) = c ∷ [] , (# c)
  flat (inl r t) with flat t
  ...| xs , prf = , r +L prf
  flat (inr l t) with flat t
  ...| xs , prf = , l +R prf
  flat (t * t') with flat t | flat t'
  ...| xs , prf | ys , prf' = , (_∙_⇒_ prf prf' refl)
  flat star[] = [] , (_ +L ε) ⋆
  flat (star-∷ t t') with flat t | flat t'
  ...| xs , prf | ys , prf' = , (_ +R (_∙_⇒_ prf prf' refl)) ⋆

  unflat : ∀ {xs e} → xs ∈[ e ] → Tree e
  unflat ε = ε
  unflat (# c) = # c
  unflat (prf ∙ prf' ⇒ eq) = unflat prf * unflat prf'
  unflat (r +L prf) = inl r (unflat prf)
  unflat (l +R prf) = inr l (unflat prf)
  unflat ((_ +L ε) ⋆) = star[]
  unflat ((_ +R (_∙_⇒_ prf prf' eq)) ⋆) = star-∷ (unflat prf) (unflat prf')


  flat-unflat : ∀ {e}(t : Tree e) → unflat (proj₂ (flat t)) ≡ t
  flat-unflat ε = refl
  flat-unflat (# c) = refl
  flat-unflat (inl r t) = cong (inl r) (flat-unflat t)
  flat-unflat (inr l t) = cong (inr l) (flat-unflat t)
  flat-unflat (t * t') = cong₂ _*_ (flat-unflat t) (flat-unflat t')
  flat-unflat star[] = refl
  flat-unflat (star-∷ t t') = cong₂ star-∷ (flat-unflat t) (flat-unflat t')


  unflat-flat : ∀ {e xs}(prf : xs ∈[ e ]) → flat (unflat prf) ≡ (xs , prf)
  unflat-flat ε = refl
  unflat-flat (# c) = refl
  unflat-flat (prf ∙ prf' ⇒ eq) rewrite eq | unflat-flat prf | unflat-flat prf' = refl
  unflat-flat (r +L prf) rewrite unflat-flat prf = refl
  unflat-flat (l +R prf) rewrite unflat-flat prf = refl
  unflat-flat ((_ +L ε) ⋆) = refl
  unflat-flat ((_ +R prf ∙ prf' ⇒ eq) ⋆) rewrite eq | unflat-flat prf | unflat-flat prf' = refl


  code : ∀ {e} → Tree e → ∃ (λ xs → xs IsBitCodeOf e)
  code ε = [] , ε
  code (# c) = [] , (# c)
  code (inl r t) with code t
  ...| ys , pr = 0# ∷ ys , inl r pr
  code (inr l t) with code t
  ...| ys , pr = 1# ∷ ys , inr l pr
  code (t * t') with code t | code t'
  ...| xs , pr | ys , pr' = xs ++ ys , pr * pr' => refl
  code star[] = 1# ∷ [] , star[]
  code (star-∷ t ts) with code t | code ts
  ...| xs , pr | xss , prs = (0# ∷ xs ++ xss) , star-∷ pr prs refl

  decode' : ∀ {xs e} → xs IsBitCodeOf e → Tree e
  decode' ε = ε
  decode' (# c) = # c
  decode' (inl r pr) = inl r (decode' pr)
  decode' (inr l pr) = inr l (decode' pr)
  decode' (pr * pr' => x) = decode' pr * decode' pr'
  decode' star[] = star[]
  decode' (star-∷ pr pr' x) = star-∷ (decode' pr) (decode' pr')

  decode : ∀ {e} → ∃ (λ xs → xs IsBitCodeOf e) → Tree e
  decode {e} (xs , pr) = decode' {xs}{e} pr

  code-decode : ∀ {e}(t : Tree e) → decode (code t) ≡ t
  code-decode ε = refl
  code-decode (# c) = refl
  code-decode (inl r t) rewrite code-decode t = refl
  code-decode (inr l t) rewrite code-decode t = refl
  code-decode (t * t') rewrite code-decode t | code-decode t' = refl
  code-decode star[] = refl
  code-decode (star-∷ t t') rewrite code-decode t | code-decode t' = refl

  bitCode2Sem : ∀ {bs e} → bs IsBitCodeOf e → ∃ (λ xs → xs ∈[ e ])
  bitCode2Sem ε = [] , ε
  bitCode2Sem (# c) = c ∷ [] , (# c)
  bitCode2Sem (inl r pr) with bitCode2Sem pr
  ...| xs , prf = xs , r +L prf
  bitCode2Sem (inr l pr) with bitCode2Sem pr
  ...| xs , prf = xs , l +R prf
  bitCode2Sem (pr * pr' => eq) with bitCode2Sem pr | bitCode2Sem pr'
  ...| xs , prf | ys , prf' = xs ++ ys , (_∙_⇒_ prf prf' refl)
  bitCode2Sem star[] = [] , (_ +L ε) ⋆
  bitCode2Sem (star-∷ pr pr' x) with bitCode2Sem pr | bitCode2Sem pr'
  ...| xs , prf | xss , prfs = xs ++ xss , (_ +R _∙_⇒_ prf prfs refl) ⋆

  sem2BitCode : ∀ {xs e} → xs ∈[ e ] → ∃ (λ bs → bs IsBitCodeOf e)
  sem2BitCode = code ∘ unflat

