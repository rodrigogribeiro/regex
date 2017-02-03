module Tool.Bindings.Primitives where
  open import IO.Primitive
  open import Data.Char
  open import Data.Bool
  open import Data.List
  open import Data.String


  {-# IMPORT System.Environment #-}

  postulate getArgs : IO (List String)

  {-# COMPILED getArgs (fmap (fmap Data.Text.pack) System.Environment.getArgs) #-}

  {-# IMPORT Data.Char #-}

  postulate isSpace : Char → Bool

  {-# COMPILED isSpace Data.Char.isSpace #-}
