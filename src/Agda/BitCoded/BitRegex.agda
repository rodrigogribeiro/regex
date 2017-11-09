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


module BitCoded.BitRegex where

    data Bit : Set where
      0# 1# : Bit

    data BitRegex : Set where
      empty  : BitRegex
      eps    : List Bit → BitRegex
      char   : List Bit → (c : Char) → BitRegex
      choice : List Bit → BitRegex → BitRegex → BitRegex
      cat    : List Bit → BitRegex → BitRegex → BitRegex
      star   : List Bit → BitRegex → BitRegex


    data _∈[[_]] : List Char → BitRegex → Set where
      eps  : ∀ bs → [] ∈[[ eps bs ]]
      char : ∀ bs c → [ c ] ∈[[ char bs c ]]
      inl  : ∀ {l xs}(r : BitRegex) bs →  xs ∈[[ l ]] → xs ∈[[ choice bs l r ]]
      inr  : ∀ {r xs}(l : BitRegex) bs →  xs ∈[[ r ]] → xs ∈[[ choice bs l r ]]
      cat  : ∀ {l r xs ys zs} bs → xs ∈[[ l ]] → ys ∈[[ r ]] → zs ≡ xs ++ ys → zs ∈[[ cat bs l r ]]
      star-[] : ∀ {l} bs → [] ∈[[ star bs l ]]
      star-∷ : ∀ {l x xs xss ys} bs → (x ∷ xs) ∈[[ l ]] → xss ∈[[ star [] l ]] → ys ≡ x ∷ xs ++ xss → ys ∈[[ star bs l ]]

    []-cat : ∀ {bs l r} → [] ∈[[ cat bs l r ]] → [] ∈[[ l ]] × [] ∈[[ r ]]
    []-cat (cat {xs = []} bs pr pr' refl) = pr , pr'
    []-cat (cat {xs = x ∷ xs} bs pr pr' ())

    char-∈-invert : ∀ {x y bs xs} → (x ∷ xs) ∈[[ char bs y ]] → x ≡ y × xs ≡ []
    char-∈-invert (char bs x) = refl , refl

    nullDec : ∀ (t : BitRegex) → Dec ([] ∈[[ t ]])
    nullDec empty = no (λ ())
    nullDec (eps bs) = yes (eps bs)
    nullDec (char bs c) = no (λ ())
    nullDec (choice bs t t') with nullDec t | nullDec t'
    ...| yes pr | pr'     = yes (inl t' bs pr) 
    ...| no pr  | yes pr' = yes (inr t bs pr')
    ...| no pr  | no pr'  = no (λ ctr → case ctr of λ{ (inl _ _ qr) → pr qr ; (inr _ _ qr) → pr' qr })
    nullDec (cat bs t t') with nullDec t | nullDec t'
    ...| yes pr | yes qr = yes (cat bs pr qr refl)
    ...| yes pr | no qr  = no (qr ∘ proj₂ ∘ []-cat)
    ...| no pr  | qr     = no (pr ∘ proj₁ ∘ []-cat)
    nullDec (star bs t') = yes (star-[] bs)


    fuse : List Bit → BitRegex → BitRegex
    fuse bs empty = empty
    fuse bs (eps x) = eps (bs ++ x)
    fuse bs (char x c) = char (bs ++ x) c
    fuse bs (choice x e e') = choice (bs ++ x) e e'
    fuse bs (cat x e e') = cat (bs ++ x) e e'
    fuse bs (star x e) = star (bs ++ x) e

    erase : BitRegex → Regex
    erase empty = ∅
    erase (eps x) = ε
    erase (char x c) = # c
    erase (choice x e e') = erase e + (erase e')
    erase (cat x e e') = erase e ∙ (erase e')
    erase (star x e) = (erase e) ⋆

    internalize : (e : Regex) → BitRegex
    internalize ∅ = empty
    internalize ε = eps [] 
    internalize (# x) = char [] x
    internalize (e ∙ e') = cat [] (internalize e) (internalize e')
    internalize (e + e') = choice [] (fuse [ 0# ] (internalize e)) (fuse [ 1# ] (internalize e'))
    internalize (e ⋆) = star [] (internalize e)

    mutual 
      erase-fuse-internalize : ∀ {bs} e → erase (fuse bs (internalize e)) ≡ e
      erase-fuse-internalize ∅ = refl
      erase-fuse-internalize ε = refl
      erase-fuse-internalize (# x) = refl
      erase-fuse-internalize (e ∙ e') rewrite internalize-erase e | internalize-erase e' = refl
      erase-fuse-internalize (e + e') rewrite erase-fuse-internalize {bs = [ 0# ]} e | erase-fuse-internalize {bs = [ 1# ]} e' = refl
      erase-fuse-internalize (e ⋆) rewrite internalize-erase e = refl

      internalize-erase : ∀ e → erase (internalize e) ≡ e
      internalize-erase ∅ = refl
      internalize-erase ε = refl
      internalize-erase (# x) = refl
      internalize-erase (e ∙ e') rewrite internalize-erase e | internalize-erase e' = refl
      internalize-erase (e + e') rewrite erase-fuse-internalize {bs = [ 0# ]} e | erase-fuse-internalize {bs = [ 1# ]} e' = refl
      internalize-erase (e ⋆) rewrite internalize-erase e = refl

    bitSemSound : ∀ {xs e} → xs ∈[[ e ]] → xs ∈[ erase e ]
    bitSemSound (eps bs) = ε
    bitSemSound (char bs c) = # c
    bitSemSound (inl r bs pr) = erase r +L bitSemSound pr
    bitSemSound (inr l bs pr) = erase l +R bitSemSound pr
    bitSemSound (cat bs pr pr₁ x) = _∙_⇒_ (bitSemSound pr) (bitSemSound pr₁) x
    bitSemSound (star-[] bs) = (_ +L ε) ⋆
    bitSemSound (star-∷ bs pr pr₁ x₁) = (_ +R (_∙_⇒_ (bitSemSound pr) (bitSemSound pr₁) x₁)) ⋆


    fuseSem : ∀ {xs} bs e → xs ∈[[ fuse bs e ]] → xs ∈[[ e ]]
    fuseSem bs empty ()
    fuseSem bs (eps x) (eps .(bs ++ x)) = eps x
    fuseSem bs (char x c) (char .(bs ++ x) .c) = char x c
    fuseSem bs (choice x e e₁) (inl .e₁ .(bs ++ x) pr) = inl e₁ x pr
    fuseSem bs (choice x e e₁) (inr .e .(bs ++ x) pr) = inr e x pr
    fuseSem bs (cat x e e₁) (cat .(bs ++ x) pr pr₁ x₁) = cat x pr pr₁ x₁
    fuseSem bs (star x e) (star-[] .(bs ++ x)) = star-[] x
    fuseSem bs (star x e) (star-∷ .(bs ++ x) pr pr' x₁) = star-∷ x pr pr' x₁


    semFuse : ∀ {xs} bs e → xs ∈[[ e ]] → xs ∈[[ fuse bs e ]]
    semFuse bs empty ()
    semFuse bs (eps x) (eps .x) = eps (bs ++ x)
    semFuse bs (char x c) (char .x .c) = char (bs ++ x) c
    semFuse bs (choice x e e₁) (inl .e₁ .x pr) = inl e₁ (bs ++ x) pr
    semFuse bs (choice x e e₁) (inr .e .x pr) = inr e (bs ++ x) pr
    semFuse bs (cat x e e₁) (cat .x pr pr₁ x₁) = cat (bs ++ x) pr pr₁ x₁
    semFuse bs (star x e) (star-[] .x) = star-[] (bs ++ x)
    semFuse bs (star x e) (star-∷ .x pr pr' x₁) = star-∷ (bs ++ x) pr pr' x₁

    bitSemComplete : ∀ {xs e} → xs ∈[ e ] → xs ∈[[ internalize e ]]
    bitSemComplete ε = eps []
    bitSemComplete (# c) = char [] c
    bitSemComplete (pr ∙ pr₁ ⇒ x) = cat [] (bitSemComplete pr) (bitSemComplete pr₁) x
    bitSemComplete (r +L pr) = inl (fuse (1# ∷ []) (internalize r)) [] (semFuse _ _ (bitSemComplete pr))
    bitSemComplete (l +R pr) = inr (fuse (0# ∷ []) (internalize l)) [] (semFuse _ _ (bitSemComplete pr))
    bitSemComplete {[]} (pr ⋆) = star-[] []
    bitSemComplete {x ∷ xs} ((.(_ ∙ _ ⋆) +L ()) ⋆)
    bitSemComplete {x ∷ xs} ((.ε +R _∙_⇒_ {xs = []} {[]} pr pr' ()) ⋆)
    bitSemComplete {x ∷ xs} ((.ε +R _∙_⇒_ {xs = []} {.x ∷ .xs} pr pr' refl) ⋆) = bitSemComplete pr'
    bitSemComplete {x ∷ .(xs₁ ++ ys)} ((.ε +R _∙_⇒_ {xs = .x ∷ xs₁} {ys} pr pr' refl) ⋆) = star-∷ [] (bitSemComplete pr) (bitSemComplete pr') refl

    bitSemComplete' : ∀ {xs} e → xs ∈[ erase e ] → xs ∈[[ e ]]
    bitSemComplete' empty ()
    bitSemComplete' (eps x) ε = eps x
    bitSemComplete' (char x c) (# .c) = char x c
    bitSemComplete' (choice x e e₁) (.(erase e₁) +L pr) = inl e₁ x (bitSemComplete' e pr)
    bitSemComplete' (choice x e e₁) (.(erase e) +R pr) = inr e x (bitSemComplete' e₁ pr)
    bitSemComplete' (cat x e e₁) (pr ∙ pr₁ ⇒ x₁) = cat x (bitSemComplete' e pr) (bitSemComplete' e₁ pr₁) x₁
    bitSemComplete' (star x e) ((.(erase e ∙ erase e ⋆) +L ε) ⋆) = star-[] x
    bitSemComplete' (star x e) ((.ε +R _∙_⇒_ {xs = []} {ys} pr pr' refl) ⋆) = bitSemComplete' _ pr'
    bitSemComplete' (star x e) ((.ε +R _∙_⇒_ {xs = x₁ ∷ xs₁} {ys} pr pr' eq) ⋆) = star-∷ x (bitSemComplete' _ pr) (bitSemComplete' _ pr') eq


    open import Base.Basics

    mkEps : ∀ {t : BitRegex} → [] ∈[[ t ]] → List Bit
    mkEps (eps bs) = bs
    mkEps (inl br bs pr) = bs ++ mkEps pr
    mkEps (inr bl bs pr) = bs ++ mkEps pr
    mkEps (cat {xs = xs}{ys = ys}bs pr pr' eq) with []-++ xs ys eq
    ...| eql , eqr rewrite eql | eqr = bs ++ mkEps pr ++ mkEps pr'
    mkEps (star-[] bs) = bs ++ [ 1# ]
    mkEps (star-∷ bs pr pr₁ x) = bs ++ [ 1# ]

    open import Derivative.Brzozowski

    bitDeriv : BitRegex → (c : Char) → BitRegex
    bitDeriv empty c = empty
    bitDeriv (eps x) c = empty
    bitDeriv (char x c) c' with c ≟C c'
    ...| yes q rewrite q = eps x 
    ...| no  q = empty 
    bitDeriv (choice x e e') c = choice x (bitDeriv e c) (bitDeriv e' c)
    bitDeriv (cat x e e') c with nullDec e 
    ...| yes p = choice x (cat x (bitDeriv e c) e') (fuse (mkEps p) (bitDeriv e' c))
    ...| no p  = cat x (bitDeriv e c) e'
    bitDeriv (star x e) c = cat x (fuse [ 0# ] (bitDeriv e c)) (star [] e)

    bitDerivSound : ∀ x xs e → xs ∈[[ bitDeriv e x ]] → (x ∷ xs) ∈[[ e ]]
    bitDerivSound x xs empty ()
    bitDerivSound x xs (eps bs) ()
    bitDerivSound x xs (char bs c) pr with c ≟C x
    bitDerivSound x [] (char bs .x) pr | yes refl = char bs x
    bitDerivSound x (y ∷ ys) (char x₂ .x) () | yes refl
    bitDerivSound x xs (char bs c) () | no q
    bitDerivSound x xs (choice bs e e') (inl .(bitDeriv e' x) .bs pr)
      = inl e' bs (bitDerivSound x xs e pr)
    bitDerivSound x xs (choice bs e e') (inr .(bitDeriv e x) .bs pr)
      = inr e bs (bitDerivSound x xs e' pr)
    bitDerivSound x xs (cat bs e e') pr with nullDec e
    bitDerivSound x xs (cat bs e e') (inl .(fuse (mkEps p) (bitDeriv e' x)) .bs (cat .bs pr pr' eq)) | yes p
      = cat bs (bitDerivSound _ _ _ pr) pr' (cong (_∷_ x) eq)
    bitDerivSound x xs (cat bs e e') (inr .(cat bs (bitDeriv e x) e') .bs pr) | yes p with fuseSem _ _ pr
    bitDerivSound x xs (cat bs e e') (inr .(cat bs (bitDeriv e x) e') .bs pr) | yes p | pr1 = cat bs p (bitDerivSound _ _ _ pr1) refl
    bitDerivSound x xs (cat bs e e') (cat .bs pr pr₁ eq) | no p = cat bs (bitDerivSound _ _ _ pr) pr₁ (cong (_∷_ x) eq)
    bitDerivSound x xs (star bs e) (cat .bs pr pr' eq) with fuseSem _ _ pr
    ...| pr1 = star-∷ bs (bitDerivSound _ _ _ pr1) pr' (cong (_∷_ x) eq)


    bitDerivComplete : ∀ x xs e → (x ∷ xs) ∈[[ e ]] → xs ∈[[ bitDeriv e x ]]
    bitDerivComplete x xs empty ()
    bitDerivComplete x xs (eps bs) ()
    bitDerivComplete x [] (char bs c) pr with c ≟C x
    ...| yes refl = eps bs
    ...| no  p = ⊥-elim (p (sym (proj₁ (char-∈-invert pr))))
    bitDerivComplete x (x₁ ∷ xs) (char x₂ c) ()
    bitDerivComplete x xs (choice bs e e') (inl .e' .bs pr) = inl (bitDeriv e' x) bs (bitDerivComplete x xs e pr)
    bitDerivComplete x xs (choice bs e e') (inr .e .bs pr) = inr (bitDeriv e x) bs (bitDerivComplete x xs e' pr)
    bitDerivComplete x xs (cat bs e e') (cat {xs = xs'}.bs pr pr₁ x₁) with nullDec e
    bitDerivComplete x xs (cat bs e e') (cat {_} {_} {[]} .bs pr pr₁ refl) | yes p = inr (cat bs (bitDeriv e x) e') bs (semFuse _ _ (bitDerivComplete _ _ _ pr₁))
    bitDerivComplete x .(xs₁ ++ _) (cat bs e e') (cat {_} {_} {.x ∷ xs₁} .bs pr pr₁ refl) | yes p
      = inl (fuse (mkEps p) (bitDeriv e' x)) bs (cat bs (bitDerivComplete _ _ _ pr) pr₁ refl)
    bitDerivComplete x xs (cat bs e e') (cat {_} {_} {[]} .bs pr pr₁ x₁) | no p = ⊥-elim (p pr)
    bitDerivComplete x .(xs₁ ++ _) (cat bs e e') (cat {_} {_} {.x ∷ xs₁} .bs pr pr₁ refl) | no p = cat bs (bitDerivComplete _ _ _ pr) pr₁ refl
    bitDerivComplete x .(xs ++ _) (star bs e) (star-∷ {x = .x} {xs} .bs pr pr₁ refl) = cat bs (semFuse _ _ (bitDerivComplete _ _ _ pr)) pr₁ refl
