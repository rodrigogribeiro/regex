open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.String

open import Function


module Tool.Parser.Arguments.Options where

  -- a type for algorithms

  data Deriv : Set where
    Antimirov  : Deriv
    Brzozowski : Deriv
    BitCodes   : Deriv


  -- a type for options

  record Options : Set where
    field
      help      : Bool
      version   : Bool
      algorithm : Deriv
      regex     : Maybe String
      files     : List String

  open Options public

  defaultOptions : Options
  defaultOptions
    = record { help      = false
             ; version   = false
             ; algorithm = Brzozowski
             ; regex     = nothing
             ; files     = []  }

  parseOptions : List String → Options
  parseOptions args = record result { files = reverse $ files result }
    where
      cons : Options → String → Options
      cons opt "-B"  = record opt { algorithm = Brzozowski }
      cons opt "-A"  = record opt { algorithm = Antimirov  }
      cons opt "-C"  = record opt { algorithm = BitCodes   }
      cons opt "-v"  = record opt { version   = true }
      cons opt "-h"  = record opt { help      = true }
      cons opt str   =
        if is-nothing (regex opt)
        then record opt { regex = just str }
        else record opt { files = str ∷ files opt }  

      result : Options
      result = foldl cons defaultOptions args
