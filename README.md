# Verified Heaps in Agda

## Goal
Build a verified Map implemented as a Heap

### Features
* Completeness Proof (Inherent to the datatype)
* Array-based heap implementation for efficiency
* Push (insert) operation
* Get operation

## Resources
I used ChatGPT as an assistant throughout this project to help me:
* Conceptualize high-level design
* Understand standard library usage
* Occasional pointers on what direction I need to take for a function
* Explaination and implementation of Postulates, big help in designing HeapOrdered

I also used the [Agda Standard Library](https://agda.github.io/agda-stdlib/v1.6/) as a resource to find functions to expedite my code.

## Challenges
I had a GREAT deal of challenges making this project. Many times functions that I thought would just be a given (parent' is a great example) took me as much as an hour.\
Here is a list of other issues I ran into
* Figuring out whether to use Fins or Nats in much of the Heap module
    * I ended up using Nat pretty often, just because the math operations with Fin were incredibly difficult
    * To overcome the unbounded nature of Nats, I made frequent use of the Maybe type
* Figuring out how to design building a Heap in a way that inductively uses the HeapOrdered proof
    * At ChatGPTs recommendation, using an empty constuctor with an easy proof to start, then just making lemmas for each operation that I used when I modified the heap to show that it maintains.
    * I didn't find the time to fully prove out these lemmas, ended up leaving them as postulates
* TIME
    * You've probably noticed, there are a fair few things I've just left as postulates with an -- Incomplete note next to it
    * Estimating the time required to do things I would normally take for granted ended up being the hardest thing
    * Even outside of specific instances, it was so constant that there would be some function that needed some translation between Nats and Fins, which would end up adding an additional 30 minutes to what should be a simple function.
    * An original goal of this project was to have it be able to be implemented in Haskell. That guided a lot of the high level design (hence why I wanted ChatGPT's help). Unfortunently, with just the limited time from so many small inconviences, I wasn't able to get to the fun part of figuring out how to translate it all to compile correctly.