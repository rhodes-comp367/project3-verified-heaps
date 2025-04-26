module Operations where

open import Heap

open import Data.Vec.Base
open import Agda.Builtin.Nat
open import Data.Fin
    using (Fin ; zero ; suc)
open import Agda.Builtin.Unit


empty : {V : Set} → Heap V
empty {V} =
  heap [] (λ ()) -- Fin Zero has no constuctors

singleton : {V : Set} → Node V → Heap V
singleton {V} n = heap (n ∷ []) proof
  where
    proof : HeapOrdered (n ∷ [])
    proof zero = tt