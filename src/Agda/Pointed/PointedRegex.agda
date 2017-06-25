open import Data.Bool    
open import Data.Char
open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Base.Regex renaming (_∙_ to _*_)
open import Base.Basics

module Pointed.PointedRegex where

  -- pointed item
  
  data PointedItem : Set where
    ∅   : PointedItem
    ε   : PointedItem
    #_  : Char → PointedItem
    !_  : Char → PointedItem
    _⊕_ : PointedItem → PointedItem → PointedItem
    _⊙_ : PointedItem → PointedItem → PointedItem
    _⋆   : PointedItem → PointedItem

  -- pointed regex

  PointedRegex : Set
  PointedRegex = PointedItem × Bool

  -- carrier of an item

  carrierItem : PointedItem → Regex
  carrierItem ∅ = ∅
  carrierItem ε = ε
  carrierItem (# x) = # x
  carrierItem (! x) = # x
  carrierItem (p ⊕ p') = carrierItem p + carrierItem p'
  carrierItem (p ⊙ p') = carrierItem p * carrierItem p'
  carrierItem (p ⋆) = (carrierItem p) ⋆

  carrierPointed : PointedRegex → Regex
  carrierPointed = carrierItem ∘ proj₁ 


  ε[_] : Bool → Set
  ε[ true ]  = ⊤
  ε[ false ] = ⊥

  -- pointed item semantics

  data _∈[[_]] : List Char → PointedItem → Set where
    !_   : (c : Char) → [ c ] ∈[[ ! c ]]  
    inl : ∀ {e xs}(e' : PointedItem) → xs ∈[[ e ]] → xs ∈[[ e ⊕ e' ]] 
    inr : ∀ {e' xs}(e : PointedItem) → xs ∈[[ e' ]] → xs ∈[[ e ⊕ e' ]]
    cinl : ∀ {e e' xs ys zs} → xs ∈[[ e ]] →
                               ys ∈[ carrierItem e' ] →
                               zs ≡ xs ++ ys → zs ∈[[ e ⊕ e' ]]
    cinr : ∀ {e e' xs} → xs ∈[[ e' ]] → xs ∈[[ e ⊙ e' ]]
    star : ∀ {e xs xss zs} → xs ∈[[ e ]] →
                             xss ∈[ (carrierItem e) ⋆ ] →
                             zs ≡ xs ++ xss → zs ∈[[ e ⋆ ]]

  -- pointed regex semantics

  _∈[[_]]p : List Char → PointedRegex → Set
  xs ∈[[ e , b ]]p = xs ∈[[ e ]] ⊎ ε[ b ]

  -- empty string aren't in any pointed item semantics.

  pointedEmpty : ∀ e → ¬ ([] ∈[[ e ]])
  pointedEmpty .(_ ⊕ e') (inl e' prf)
    = pointedEmpty _ prf
  pointedEmpty .(e ⊕ _) (inr e prf)
    = pointedEmpty _ prf
  pointedEmpty .(_ ⊕ _) (cinl {xs = xs}{ys = ys} prf x eq) with []-++ xs ys eq
  ...| p , q rewrite p | q = pointedEmpty _ prf
  pointedEmpty .(_ ⊙ _) (cinr prf) = pointedEmpty _ prf
  pointedEmpty .(_ ⋆) (star {xs = xs}{xss = xss} prf x eq) with []-++ xs xss eq
  ...| p , q rewrite p | q = pointedEmpty _ prf


  pRegexEmptyL : ∀ e b → [] ∈[[ e , b ]]p → b ≡ true
  pRegexEmptyL e false (inj₁ x) = ⊥-elim (pointedEmpty _ x)
  pRegexEmptyL e false (inj₂ ())
  pRegexEmptyL e true prf = refl

  pRegexEmptyR : ∀ e b → b ≡ true → [] ∈[[ e , b ]]p
  pRegexEmptyR e b eq rewrite eq = inj₂ tt

  -- broadcasting points

  _∥_ : PointedRegex → PointedRegex → PointedRegex
  (e , b) ∥ (e' , b') = e ⊕ e' , b ∨ b'

  ∙-lift : (e e' : PointedItem)(b b' : Bool) → PointedRegex

  ∙[_] : PointedItem → PointedRegex
  ∙[ ∅ ] = ∅ , false
  ∙[ ε ] = ε , true
  ∙[ # x ] = ! x , false
  ∙[ ! x ] = ! x , false
  ∙[ e ⊕ e' ] = ∙[ e ] ∥ ∙[ e' ]
  ∙[ e ⊙ e' ] with ∙[ e ]
  ...| e1 , b = ∙-lift e1 e' b false
  ∙[ e ⋆ ] with ∙[ e ]
  ...| e1 , b = e1 ⋆ , true
  

  ∙-lift e e' false b' = e ⊙ e' , b'
  ∙-lift e e' true b' with ∙[ e' ]
  ...| e2 , b2 = e ⊙ e2 , b' ∨ b2


  ∙[[_]] : PointedRegex → PointedRegex
  ∙[[ e , b ]] with ∙[ e ]
  ...| e1 , b1 = e1 , b ∨ b1
  

  -- broadcastSound : ∀ {xs} e → xs ∈[[ e , b ]]
