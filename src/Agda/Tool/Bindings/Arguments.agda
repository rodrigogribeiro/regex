open import Data.List
open import Data.String

open import IO

module Tool.Bindings.Arguments where

  import Tool.Bindings.Primitives as P

  getArgs : IO (List String)
  getArgs = lift P.getArgs
