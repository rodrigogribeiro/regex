module Teste

%default total

data RegExp : Type where
  Zero : RegExp
  Eps  : RegExp
  Chr  : Nat -> RegExp
  Cat  : RegExp -> RegExp -> RegExp 
  Alt  : RegExp -> RegExp -> RegExp 
  Star : RegExp -> RegExp 

data InRegExp : List Nat -> RegExp -> Type where
  InEps : InRegExp [] Eps
  InChr : InRegExp [ a ] (Chr a)
  InCat : InRegExp xs l ->
          InRegExp ys r ->
          zs = xs ++ ys ->
          InRegExp zs (Cat l r)
  InAltL : InRegExp xs l ->
           InRegExp xs (Alt l r)
  InAltR : InRegExp xs r ->
           InRegExp xs (Alt l r)
  InStar : InRegExp xs (Alt Eps (Cat e (Star e))) ->
           InRegExp xs (Star e)

inZeroInv : InRegExp xs Zero -> Void
inZeroInv InEps impossible

inEpsInv : InRegExp xs Eps -> xs = []
inEpsInv InEps = Refl

inEpsCons : InRegExp (x :: xs) Eps -> Void
inEpsCons InEps impossible

inChrNil : InRegExp [] (Chr c) -> Void
inChrNil InEps impossible

concatNil : Prelude.List.Nil = (xs ++ ys) -> (xs = Prelude.List.Nil , ys = Prelude.List.Nil)
concatNil {xs = []}{ys = []} p = (Refl, Refl)
concatNil {xs = []}{ys = (x :: xs)} p = void (lemma_val_not_nil (sym p))
concatNil {xs = (x :: xs)}{ys = ys} p = void (lemma_val_not_nil (sym p))

inCatNil : InRegExp [] (Cat e e') -> (InRegExp [] e , InRegExp [] e')
inCatNil (InCat x y prf) with (concatNil prf)
  inCatNil (InCat x y prf) | (Refl , Refl) = (x, y)

inAltNil : InRegExp [] (Alt e e') -> Either (InRegExp [] e) (InRegExp [] e')
inAltNil (InAltL x) = Left x
inAltNil (InAltR x) = Right x


appendNilR : (xs : List a) -> xs = xs ++ []
appendNilR [] = Refl
appendNilR (x :: xs) = cong (appendNilR xs)

inRegLemma : InRegExp xs1 e -> xs = xs1 ++ [] -> InRegExp xs e
inRegLemma {xs1} pr eq with (trans (appendNilR xs1) (sym eq))
                 | Refl = pr
infixl 4 .|.

(.|.) : RegExp -> RegExp -> RegExp
Zero .|. e = e
e .|. Zero = e
e .|. e'   = Alt e e'

infixl 5 .@.

(.@.) : RegExp -> RegExp -> RegExp
Zero .@. e = Zero
Eps .@. e  = e
e .@. Zero = Zero
e .@. Eps  = e
e .@. e'   = Cat e e'

star : RegExp -> RegExp
star Zero = Eps
star Eps = Eps
star e = Star e

altOptSound : (l : RegExp)     ->
              (r : RegExp)     ->
              (xs : List Nat) ->
              InRegExp xs (l .|. r) ->
              InRegExp xs (Alt l r)
altOptSound Zero r xs pr = InAltR pr
altOptSound Eps Zero xs pr = InAltL pr
altOptSound Eps Eps xs pr = pr
altOptSound Eps (Chr x) xs pr = pr
altOptSound Eps (Cat x y) xs pr = pr
altOptSound Eps (Alt x y) xs pr = pr
altOptSound Eps (Star x) xs pr = pr
altOptSound (Chr x) Zero xs pr = InAltL pr
altOptSound (Chr x) Eps xs pr = pr
altOptSound (Chr x) (Chr y) xs pr = pr
altOptSound (Chr x) (Cat y z) xs pr = pr
altOptSound (Chr x) (Alt y z) xs pr = pr
altOptSound (Chr x) (Star y) xs pr = pr
altOptSound (Cat x y) Zero xs pr = InAltL pr
altOptSound (Cat x y) Eps xs pr = pr
altOptSound (Cat x y) (Chr z) xs pr = pr
altOptSound (Cat x y) (Cat z w) xs pr = pr
altOptSound (Cat x y) (Alt z w) xs pr = pr
altOptSound (Cat x y) (Star z) xs pr = pr
altOptSound (Alt x y) Zero xs pr = InAltL pr
altOptSound (Alt x y) Eps xs pr = pr
altOptSound (Alt x y) (Chr z) xs pr = pr
altOptSound (Alt x y) (Cat z w) xs pr = pr
altOptSound (Alt x y) (Alt z w) xs pr = pr
altOptSound (Alt x y) (Star z) xs pr = pr
altOptSound (Star x) Zero xs pr = InAltL pr
altOptSound (Star x) Eps xs pr = pr
altOptSound (Star x) (Chr y) xs pr = pr
altOptSound (Star x) (Cat y z) xs pr = pr
altOptSound (Star x) (Alt y z) xs pr = pr
altOptSound (Star x) (Star y) xs pr = pr

altOptComplete : (l : RegExp)  ->
                 (r : RegExp)  ->
                 (xs : List Nat) ->
                 InRegExp xs (Alt l r) ->
                 InRegExp xs (l .|. r)
altOptComplete Zero r xs (InAltL x) = void (inZeroInv x)
altOptComplete Zero r xs (InAltR x) = x
altOptComplete Eps Zero xs (InAltL x) = x
altOptComplete Eps Zero xs (InAltR x) = void (inZeroInv x)
altOptComplete Eps Eps xs pr = pr
altOptComplete Eps (Chr x) xs pr = pr
altOptComplete Eps (Cat x y) xs pr = pr
altOptComplete Eps (Alt x y) xs pr = pr
altOptComplete Eps (Star x) xs pr = pr
altOptComplete (Chr x) Zero xs (InAltL y) = y
altOptComplete (Chr x) Zero xs (InAltR y) = void (inZeroInv y)
altOptComplete (Chr x) Eps xs pr = pr
altOptComplete (Chr x) (Chr y) xs pr = pr
altOptComplete (Chr x) (Cat y z) xs pr = pr
altOptComplete (Chr x) (Alt y z) xs pr = pr
altOptComplete (Chr x) (Star y) xs pr = pr
altOptComplete (Cat x y) Zero xs (InAltL z) = z
altOptComplete (Cat x y) Zero xs (InAltR z) = void (inZeroInv z)
altOptComplete (Cat x y) Eps xs pr = pr
altOptComplete (Cat x y) (Chr z) xs pr = pr
altOptComplete (Cat x y) (Cat z w) xs pr = pr
altOptComplete (Cat x y) (Alt z w) xs pr = pr
altOptComplete (Cat x y) (Star z) xs pr = pr
altOptComplete (Alt x y) Zero xs (InAltL z) = z
altOptComplete (Alt x y) Zero xs (InAltR z) = void (inZeroInv z)
altOptComplete (Alt x y) Eps xs pr = pr
altOptComplete (Alt x y) (Chr z) xs pr = pr
altOptComplete (Alt x y) (Cat z w) xs pr = pr
altOptComplete (Alt x y) (Alt z w) xs pr = pr
altOptComplete (Alt x y) (Star z) xs pr = pr
altOptComplete (Star x) Zero xs (InAltL y) = y
altOptComplete (Star x) Zero xs (InAltR y) = void (inZeroInv y)
altOptComplete (Star x) Eps xs pr = pr
altOptComplete (Star x) (Chr y) xs pr = pr
altOptComplete (Star x) (Cat y z) xs pr = pr
altOptComplete (Star x) (Alt y z) xs pr = pr
altOptComplete (Star x) (Star y) xs pr = pr

catOptSound : (l : RegExp) ->
              (r : RegExp) ->
              (xs : List Nat) ->
              InRegExp xs (l .@. r) ->
              InRegExp xs (Cat l r)
catOptSound Zero r xs pr = void (inZeroInv pr)
catOptSound Eps r xs pr = InCat InEps pr Refl
catOptSound (Chr x) Zero xs pr = void (inZeroInv pr)
catOptSound (Chr x) Eps xs pr = InCat pr InEps (appendNilR xs)
catOptSound (Chr x) (Chr y) xs pr = pr
catOptSound (Chr x) (Cat y z) xs pr = pr
catOptSound (Chr x) (Alt y z) xs pr = pr
catOptSound (Chr x) (Star y) xs pr = pr
catOptSound (Cat x y) Zero xs pr = void (inZeroInv pr)
catOptSound (Cat x y) Eps xs pr = InCat pr InEps (appendNilR xs)
catOptSound (Cat x y) (Chr z) xs pr = pr
catOptSound (Cat x y) (Cat z w) xs pr = pr
catOptSound (Cat x y) (Alt z w) xs pr = pr
catOptSound (Cat x y) (Star z) xs pr = pr
catOptSound (Alt x y) Zero xs pr = void (inZeroInv pr)
catOptSound (Alt x y) Eps xs pr = InCat pr InEps (appendNilR xs)
catOptSound (Alt x y) (Chr z) xs pr = pr
catOptSound (Alt x y) (Cat z w) xs pr = pr
catOptSound (Alt x y) (Alt z w) xs pr = pr
catOptSound (Alt x y) (Star z) xs pr = pr
catOptSound (Star x) Zero xs pr = void (inZeroInv pr)
catOptSound (Star x) Eps xs pr = InCat pr InEps (appendNilR xs)
catOptSound (Star x) (Chr y) xs pr = pr
catOptSound (Star x) (Cat y z) xs pr = pr
catOptSound (Star x) (Alt y z) xs pr = pr
catOptSound (Star x) (Star y) xs pr = pr


catOptComplete : (l : RegExp) ->
                 (r : RegExp) ->
                 (xs : List Nat) ->
                 InRegExp xs (Cat l r) ->
                 InRegExp xs (l .@. r)
catOptComplete Zero r xs (InCat x y prf) = void (inZeroInv x)
catOptComplete Eps r xs (InCat InEps y Refl) = y
catOptComplete (Chr x) Zero xs (InCat y z prf) = void (inZeroInv z)
catOptComplete (Chr x) Eps xs (InCat y InEps prf) = inRegLemma y prf
catOptComplete (Chr x) (Chr y) xs pr = pr
catOptComplete (Chr x) (Cat y z) xs pr = pr
catOptComplete (Chr x) (Alt y z) xs pr = pr
catOptComplete (Chr x) (Star y) xs pr = pr
catOptComplete (Cat x y) Zero xs (InCat z w prf) = void (inZeroInv w)
catOptComplete (Cat x y) Eps xs (InCat z InEps prf) = inRegLemma z prf
catOptComplete (Cat x y) (Chr z) xs pr = pr
catOptComplete (Cat x y) (Cat z w) xs pr = pr
catOptComplete (Cat x y) (Alt z w) xs pr = pr
catOptComplete (Cat x y) (Star z) xs pr = pr
catOptComplete (Alt x y) Zero xs (InCat z w prf) = void (inZeroInv w)
catOptComplete (Alt x y) Eps xs (InCat z InEps prf) = inRegLemma z prf
catOptComplete (Alt x y) (Chr z) xs pr = pr
catOptComplete (Alt x y) (Cat z w) xs pr = pr
catOptComplete (Alt x y) (Alt z w) xs pr = pr
catOptComplete (Alt x y) (Star z) xs pr = pr
catOptComplete (Star x) Zero xs (InCat y z prf) = void (inZeroInv z)
catOptComplete (Star x) Eps xs (InCat y InEps prf) = inRegLemma y prf
catOptComplete (Star x) (Chr y) xs pr = pr
catOptComplete (Star x) (Cat y z) xs pr = pr
catOptComplete (Star x) (Alt y z) xs pr = pr
catOptComplete (Star x) (Star y) xs pr = pr

starOptSound : (l : RegExp) ->
               (xs : List Nat) ->
               InRegExp xs (star l) ->
               InRegExp xs (Star l)
starOptSound Zero xs pr = InStar (InAltL pr)
starOptSound Eps xs pr = InStar (InAltL pr)
starOptSound (Chr x) xs pr = pr
starOptSound (Cat x y) xs pr = pr
starOptSound (Alt x y) xs pr = pr
starOptSound (Star x) xs pr = pr

starOptComplete : (l : RegExp) ->
                  (xs : List Nat) ->
                  InRegExp xs (Star l) ->
                  InRegExp xs (star l)
starOptComplete Zero xs (InStar (InAltL x)) = x
starOptComplete Zero xs (InStar (InAltR (InCat x y prf))) = void (inZeroInv x)
starOptComplete Eps xs (InStar (InAltL x)) = x
starOptComplete Eps xs (InStar (InAltR (InCat InEps y Refl))) = starOptComplete _ xs y
starOptComplete (Chr x) xs pr = pr
starOptComplete (Cat x y) xs pr = pr
starOptComplete (Alt x y) xs pr = pr
starOptComplete (Star x) xs pr = pr

hasEmptyDec : (e : RegExp) -> Dec (InRegExp [] e)
hasEmptyDec Zero = No (void . inZeroInv)
hasEmptyDec Eps = Yes InEps
hasEmptyDec (Chr c) = No inChrNil
hasEmptyDec (Cat e e') with (hasEmptyDec e)
  hasEmptyDec (Cat e e') | (Yes prf) with (hasEmptyDec e')
    hasEmptyDec (Cat e e') | (Yes prf) | (Yes prf') = Yes (InCat prf prf' Refl)
    hasEmptyDec (Cat e e') | (Yes prf) | (No contra) = No (contra . snd . inCatNil)
  hasEmptyDec (Cat e e') | (No contra) = No (contra . fst . inCatNil)
hasEmptyDec (Alt e e') with (hasEmptyDec e)
  hasEmptyDec (Alt e e') | (Yes prf) = Yes (InAltL prf)
  hasEmptyDec (Alt e e') | (No contra) with (hasEmptyDec e')
    hasEmptyDec (Alt e e') | (No contra) | (Yes prf) = Yes (InAltR prf)
    hasEmptyDec (Alt e e') | (No contra) | (No f) = No (void . either contra f . inAltNil)
hasEmptyDec (Star e) = Yes (InStar (InAltL InEps))


-- derivative definition

deriv : (e : RegExp) -> Nat -> RegExp
deriv Zero c = Zero
deriv Eps c = Zero
deriv (Chr c') c with (decEq c' c)
  deriv (Chr c) c  | Yes Refl = Eps
  deriv (Chr c') c | No nprf = Zero
deriv (Alt l r) c = (deriv l c) .|. (deriv r c)
deriv (Star e) c = (deriv e c) .@. (star e)
deriv (Cat l r) c with (hasEmptyDec l)
  deriv (Cat l r) c | Yes prf = ((deriv l c) .@. r) .|. (deriv r c)
  deriv (Cat l r) c | No nprf = (deriv l c) .@. r


derivComplete : InRegExp (x :: xs) e -> InRegExp xs (deriv e x) 
derivComplete {e = Zero}{xs = xs}{x = x} pr = void (inZeroInv pr)
derivComplete {e = Eps}{xs = xs}{x = x} pr with (inEpsInv pr)
  derivComplete {e = Eps}{xs = xs}{x = x} pr | eq = void (lemma_val_not_nil eq)
derivComplete {e = (Chr y)}{xs = xs}{x = x} pr with (decEq y x)
  derivComplete {e = (Chr x)}{xs = []}{x = x} InChr | (Yes Refl) = InEps
  derivComplete {e = (Chr x)}{xs = []}{x = x} InChr | (No contra) = void (contra Refl)
derivComplete {e = (Cat y z)}{xs = xs}{x = x} pr with (hasEmptyDec y)
  derivComplete {e = (Cat y z)}{xs = xs}{x = x} (InCat {xs = []} w s Refl) | (Yes prf)
    = altOptComplete (deriv y x .@. z) (deriv z x) xs (InAltR (derivComplete s))
  derivComplete {e = (Cat y z)}{xs = ys ++ ys1}{x = x} (InCat {xs = (x :: ys)}{ys = ys1} w s Refl)
    | (Yes prf) 
      = altOptComplete (deriv y x .@. z) (deriv z x) _
                       (InAltL (catOptComplete (deriv y x) z (ys ++ ys1)
                                (InCat (derivComplete w) s Refl)))
  derivComplete {e = (Cat y z)}{xs = xs}{x = x} (InCat {xs = []} w s eq) | (No contra)
      = void (contra w)
  derivComplete {e = (Cat y z)}{xs = ys ++ ys1}{x = x} (InCat {xs = (x :: ys)}{ys = ys1} w s Refl)
    | (No contra)
      = catOptComplete (deriv y x) z (ys ++ ys1) (InCat (derivComplete w) s Refl)
derivComplete {e = (Alt e e')}{xs = xs}{x = x} (InAltL y)
  = altOptComplete (deriv e x) (deriv e' x) xs (InAltL (derivComplete y))
derivComplete {e = (Alt e e')}{xs = xs}{x = x} (InAltR y)
  = altOptComplete (deriv e x) (deriv e' x) xs (InAltR (derivComplete y))
derivComplete {e = Star _}{xs = _}{x = _}(InStar (InAltL InEps)) impossible
derivComplete {e = Star e'}{xs = xs}{x = x}(InStar (InAltR (InCat {zs = x :: xs}{xs = []}{ys = x :: xs} y z Refl))) = derivComplete z
derivComplete {e = Star e'}{xs = xs1 ++ ys1}{x = x}(InStar (InAltR (InCat {zs = (x :: (xs1 ++ ys1))}{xs = x :: xs1}{ys = ys1} y z Refl))) 
  = catOptComplete (deriv e' x) 
                   (star e') 
                   (xs1 ++ ys1) 
                   (InCat (derivComplete y) (starOptComplete _ _ z) Refl)
derivComplete {e = Star _}{xs = _}{x = _}(InStar (InAltR (InCat {xs = []}{ys = []} _ _ Refl)))
  impossible
