module Operations where

open import Heap

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Data.Fin
    using (Fin ; zero ; suc)
    renaming (toℕ to toNat)
    renaming (fromℕ< to fromNat<)
    renaming (fromℕ to fromNat)
open import Data.Vec.Base
open import Data.Nat.Base
    using (⌊_/2⌋)
open import Data.Nat.Properties
    using (_≤?_)
open import Relation.Binary.PropositionalEquality.Core
    using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary
    using (Dec ; _because_ ; Reflects)
open import Data.Nat.DivMod
    using (_/_)



---- ASSORTED HELPERS ----

removeLast : {V : Set} → {n : Nat} → Vec V (suc n) → Vec V n
removeLast (x ∷ []) = []
removeLast (x ∷ y ∷ vs) = x ∷ removeLast (y ∷ vs)

-- Append
snoc : {V : Set} → {n : Nat} → V → Vec V n → Vec V (suc n)
snoc V [] = V ∷ []
snoc V (x ∷ v) = x ∷ snoc V v

-- Get the index of the last spot in a vector as a Fin
last-index : {V : Set} {n : Nat} → Vec V (suc n) 
    → Fin (suc n)
last-index (_ ∷ []) = zero
last-index (_ ∷ x ∷ xs) = suc (last-index (x ∷ xs))


---- HEAP HELPERS ----

parent : Nat → Nat
parent i = ⌊(i - 1) /2⌋ -- better optimized divide by 2, without needing div

{-
postulate
  parent-f< : ∀ {n} (f : Fin (suc n)) → parent (toℕ f) < suc n
-}

-- Literally just a version of parent using Fins, but I spent literally an hour on this, so I'm leaving it.
-- Tried to use fromNat<, thinking that a proof that subtracting then dividing something by two makes it less than it was originally would be trivial
-- Kept running into annoying conversion steps all the time, had a hard time even when I tried to make it a postulate
postulate
    parent' : {n : Nat} → Fin (suc n) → Fin (suc n)


left : Nat → Nat
left i = 2 * i + 1

right : Nat → Nat
right i = 2 * i + 2

swap : {V : Set} → {n : Nat} → Fin n → Fin n → Vec (Node V) n
    → Vec (Node V) n
swap i j vec = updateAt i (λ x → vj) (updateAt j (λ x → vi) vec)
    where
    vi = lookup vec i
    vj = lookup vec j

-- To be used after an insertion to get back to being heap ordered
bubble-up : {V : Set} → {n : Nat} → Vec (Node V) (suc n) → Fin (suc n) 
    → Vec (Node V) (suc n)
bubble-up vec zero = vec                                            -- root
bubble-up vec k = swap k (parent' k) vec
  where
    child = lookup vec k
    par = lookup vec k


-- To be used in deletions
postulate
    shift-down : {V : Set} → {n : Nat} → Vec (Node V) (suc n) → Nat
        → Vec (Node V) (suc n)
    -- Incomplete

---- HELPER PROOFS ----

-- Implementation of proofs incomplete
postulate
    swap-node-preserves : {V : Set} → {n : Nat} → (vec : Vec (Node V) n) → (i j : Fin n)
        → HeapOrdered vec  -- previous proof
        → ∀ (k : Fin n) → (k ≢ i) → (k ≢ j) -- For all indicies that might be around it
        → NodeHeapOrdered (swap i j vec) (toNat k) (lookup (swap i j vec) k) -- The node that might be around the swapped ones still work

    bubble-up-preserves : ∀ {V : Set} {n : Nat} {node : Node V} {vec : Vec (Node V) n}
        → HeapOrdered vec
        → HeapOrdered (bubble-up (snoc node vec) (last-index (snoc node vec)))

---- HEAP INFO OPERATIONS ----

size : {V : Set} → Heap V → Nat
size (heap vec _) = length vec

getKey' : {V : Set} → {n : Nat} → Nat → Vec (Node V) n → Maybe V
getKey' _ [] = nothing
getKey' n (x ∷ v) with n == Node.key x
... | true = just (Node.val x)
... | false = getKey' n v

getKey : {V : Set} → Nat → Heap V → Maybe V
getKey n (heap vec _) = getKey' n vec

containsKey : {V : Set} → Nat → Heap V → Bool
containsKey i h with getKey i h
... | nothing = false
... | just _ = true 

---- HEAP MUTABLE OPERATIONS ----

push : {V : Set} → Node V → Heap V → Heap V
push n (heap vec order) = heap (bubble-up newVec (last-index newVec)) ((bubble-up-preserves order))
    where
    newVec = snoc n vec

postulate
    deleteKey : {V : Set} → Nat → Heap V → Heap V
-- Incomplete

---- CONSTRUCTORS ----

empty : {V : Set} → Heap V
empty {V} =
  heap [] (λ ()) -- Fin Zero has no constuctors

singleton : {V : Set} → Node V → Heap V
singleton {V} n = heap (n ∷ []) proof
  where
    proof : HeapOrdered (n ∷ [])
    proof zero = tt

heapFromList : {V : Set} → List (Node V) → Heap V
heapFromList [] = empty
heapFromList (x ∷ l) = push x (heapFromList l)