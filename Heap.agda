module Heap where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.Nat.Base
    using (_≤_)
open import Data.Vec.Base
open import Relation.Nullary
    using (Dec ; yes ; no)
open import Data.Fin
    using (Fin ; zero ; suc)
    renaming (toℕ to toNat)


record Node (V : Set) : Set where
    constructor node
    field
        key : Nat -- Using Nat to make conparisions work in Haskell
        val : V

data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

nat-lookup : {A : Set}{n : Nat} → Nat → Vec A n → Maybe A
nat-lookup zero (x ∷ _) = just x
nat-lookup (suc k) (_ ∷ xs) = nat-lookup k xs
nat-lookup _ [] = nothing

data _×_ (A B : Set) : Set where
  _,_ : A → B
    → A × B

NodeHeapOrdered
  : {V : Set} → {len : Nat}
  → Vec (Node V) len   -- heap vec
  → Nat                -- parent index i
  → Node V             -- parent node
  → Set                -- proposition about that node
NodeHeapOrdered vec i p with nat-lookup (2 * i + 1) vec | nat-lookup (2 * i + 2) vec
... | nothing | nothing = ⊤
... | nothing | just r  = Node.key r ≤ Node.key p
... | just l  | nothing = Node.key l ≤ Node.key p
... | just l  | just r  = (Node.key l ≤ Node.key p) × (Node.key r ≤ Node.key p)

HeapOrdered : {V : Set} → {len : Nat} → Vec (Node V) len → Set
HeapOrdered {_} {len} vec = ∀ (i : Fin len) → NodeHeapOrdered vec (toNat i) (lookup vec i)


record Heap (V : Set) : Set where
    constructor heap
    field
        {len} : Nat
        vec : Vec (Node V) len
        order : HeapOrdered vec