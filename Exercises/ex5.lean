/-
COMP2012 (LAC) 2026

Exercise 5

Construct a CFG and PDA for the language of bracket-matched
words.

Don't change anything else in this file!
-/
import Proofs.CFG
import Mathlib.Tactic.DeriveFintype
import Proofs.PDA

namespace ex5

open Lang Sum Cfg CFG Pda PDA

/-
Let SigmaPar be the alphabet of left and right brackets
-/

inductive SigmaPar : Type
| lpar -- "⟨"
| rpar -- "⟩"
deriving Fintype, DecidableEq
open SigmaPar

/-
We consider the language L : Lang Σ of bracket-matched words, words
words in which every ⟨ is “closed” by a ⟩ occurring later in the word. For instance:
• [] ∈ L -- ϵ ∈ L
• [lpar,rpar] ∈ L -- ⟨⟩ ∈ L
• [lpar,lpar,rpar,lpar,rpar,rpar] ∈ L -- ⟨⟩⟨⟩ ∈ L
• [lpar,lpar,rpar] ∉ L   -- ⟨⟨⟩ ∉ L because it has more ⟨’s than ⟩’s,
• [lpar,rpar,rpar] ∉ L   -- ⟨⟩⟩ ∉ L because it has more ⟩’s than ⟨’s,
• [lpar,rpar,rpar,lpar] ∉ L -- ⟨⟩⟩⟨ ∉ L because the second ⟩ occurs before the corresponding ⟨.
-/

/- 1. Define a CFG for the language, you will also need to define an inductive type for the Non-terminals -/
inductive NTPar : Type
-- E.g. | NT1 | NT2 | ...
deriving Fintype, DecidableEq
open NTPar

abbrev GPar : CFG SigmaPar
:= { NT := sorry
     S := sorry
     P := sorry
}

/- 2. Define a PDA for the language -/
-- You need to define inductive types for the states and the stack alphabet
inductive QPar : Type
-- E.g. | q0 | q1 | ...
deriving Fintype, DecidableEq
open QPar

inductive ΓPar : Type
-- E.g. | g0 | g1 | ...
deriving Fintype, DecidableEq
open ΓPar

abbrev PPar : PDA SigmaPar
:= { Q := sorry
     Γ := sorry
     s := sorry
     Z₀ := sorry
     F := sorry
     δ q x z := sorry
}

-- 3. Show that ⟨⟩⟨⟩ ∈ L PPar
-- you can either do this by spelling out the sequence of IDs in a comment or by proving
theorem e3 : [SigmaPar.lpar,SigmaPar.lpar, SigmaPar.rpar,SigmaPar.lpar,SigmaPar.rpar, SigmaPar.rpar] ∈ L PPar := by
     sorry
-- in Lean.

/-
⟨⟩⟨⟩ ∈ L PPar because:
(q0, lpar lpar rpar lpar rpar rpar, hash) ->
...
-/
end ex5
