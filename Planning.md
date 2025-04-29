# Planning Final Heap Project

## Goal
Make a verified Map Heap datatype that can be used in Haskell
(Max heap)
## Primary Data Structure
To create a heap you have to supply:
A Vector of the items
Proof of Structure Property
Proof of Heap-Order Property

The Key to the should be a type that is easily comparable to ensure the less than, but the value should be able to be anything of type set. 
*TODO* Research how this should work for compatibility with Haskell
### Vector Type
We use a vector because its encoding of a length should be useful in the existence checks that the properties need to do
### Structure Property
Needs to prove that it is a complete binary tree.
Essentially, if a Node (part of the vec) lacks a child (2n or 2n+1), then all following nodes also lack children

This should be really easy with a vector-based model, since we just need to basically show that there are no blank spots in the vector, since adding an item will expand vector size by 1
### Heap-Order Property
This is the difficult one. Need to prove that for all items in the vec, its children at 2n and 2n+1 are either non existent or are less than the current one. 
This can use a with clause and a separate function that looks into the existence of a child as a Dec type.

## Operations
Need to add as many of these as time allows after creating the main heap type with its proofs. The inclusion of proofs into the heap type should ensure that an operation has made a valid heap

Each operations can come with its own proof that it does what it says it should correctly. 