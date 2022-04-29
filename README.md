# Streams of Approximations, Equivalence of Recursive Effectful Programs 
## Niccolò Veltri and Niels Voorneveld

Behavioural equivalence for functional languages with algebraic effects and general recursion is often difficult to formalize. 
When modelling the behaviour of higher-order programs, one often needs to employ multiple coinductive structures simultaneously.
In this paper, we aim to simplify the issue with a single external stream monad dealing with recursion, and deal with the structures for modelling higher-order types in a purely inductive (finite) manner. We take a page from classical domain theory, modelling recursive programs as limits of increasing sequences of ``finite'' denotational elements. 

We carry around a single relation which contains all relevant information of behaviour: self-related elements are considered correct according to the denotational semantics, and two elements that are related both ways are considered equivalent. We implement equivalence of effectful programs using a relation lifting, creating a notion of behavioural equivalence for approximations. This is lifted to behavioural equivalence for recursive programs modelled by sequences of approximations, using a relator implementing a notion of weak similarity. We apply this to a fragment of call-by-push-value lambda calculus with algebraic effects, and establish a denotational equivalence which is sound with respect to an operational semantics, and sound with respect to contextual equivalence.

The file [Everything.agda](https://github.com/Voorn/Stream-Equivalence/Everything.agda) contains the whole Agda development.