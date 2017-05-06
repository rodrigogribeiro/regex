module BitCoded.Recursion where

  Rel : Set → Set₁
  Rel A = A → A → Set

  -- accessibility predicate

  data Acc {A : Set}(_<_ : Rel A)(x : A) : Set where
    acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

  WellFounded : ∀ {A : Set} → Rel A → Set
  WellFounded _<_ = ∀ x → Acc _<_ x

  module NatRecursion where

    open import Data.Nat hiding (_<_) renaming (_<′_ to _<_)

    <-ℕ-wf : WellFounded _<_
    <-ℕ-wf x = acc (aux x)
               where
                 aux : ∀ x y → y < x → Acc _<_ y
                 aux .(suc y) y ≤′-refl = <-ℕ-wf y
                 aux (suc x) y (≤′-step pr) = aux x y pr
        
  module InverseImageRecursion {A B}(_<_ : Rel B)(f : A → B) where

    _<<_ : Rel A
    x << y = f x < f y

    ii-acc : ∀ {x} → Acc _<_ (f x) → Acc _<<_ x
    ii-acc  (acc g) = acc (λ y fy<fx → ii-acc (g (f y) fy<fx))

    ii-wf : WellFounded _<_ → WellFounded _<<_
    ii-wf wf x = ii-acc (wf (f x))

  module <-OnLengthRecursion (A : Set) where

    open NatRecursion
    open import Data.List
    open import Data.Nat hiding (_<_) renaming (_<′_ to _<_)
    open InverseImageRecursion {A = List A} _<_ length public

    wf : WellFounded _<<_
    wf = ii-wf <-ℕ-wf
