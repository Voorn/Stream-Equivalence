module Everything where


-- This is the Agda formalisation for the paper submission to MPC 2022,
-- Title: Streams of Approximations, Equivalence of Recursive Effectful Programs.
-- Authors: Niccolo Veltri and Niels Voorneveld
-- The comments make explicit reference to sections, definitions, examples,
-- and results from this paper.
-- Code compiles in Agda version 2.6.1


-- Formulation of our treatment of relations
import Cat-Rel


-- Part I: The 2 main monads used

-- Stream monad and their properties
import Stream

-- Monad of S-terms
import S-Trees



-- Part II: Relators (Section 4 up to Subsection 4.1)

-- Relators on S-Trees in general and their properties.
-- Contains the syntactic relator and the nondeterministic relator
import Relator

-- Other examples of relators, including the stateful relator
import Relator-by-Partial-Runner



-- Part III: A Call-by-push-Value language and their denotations

-- Formulation of CBPV with denotations (Section 3)
import CBPV

-- Improvement order for CBPV (Subsection 4.1)
-- + the full behavioural relation from Definition 10
import CBPV-Order



-- Part IV: Properties of the full program denotation (Section 5)

-- Theorem 1. The behavioural relation
import CBPV-Precong

-- Lemma 7. The substitution lemma
import CBPV-substitution

-- Theorem 2. Soundness of the behavioural relation
import CBPV-soundness
