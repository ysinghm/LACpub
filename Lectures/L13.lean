import Proofs.Lang
import Mathlib.Tactic.DeriveFintype

namespace pda

open Lang Lang.Examples SigmaABC
variable (Sigma : Type)[Alphabet Sigma]

-- What have we seen so far?
/-
Chomsky Hierarchy
Level 3: Regular languages
A language that can be represented by:
 - a DFA
 - an NFA
 - A regular expression

Level 2: Context-free languages
 - Context-free grammars
 - Pushdown automata

NFA/DFA: Automata with limited memory
Pushdown automata: NFA + stack
-/
abbrev anbn : Lang SigmaABC
:= { a^n ++ b^n | (n : ℕ) }

structure PDA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- Stack alphabet
  [alphΓ : Alphabet Γ]
  s : Q -- initial state
  z₀ : Γ -- initial stack state
  F : Finset Q -- set of final states
  δ : Q → Option Sigma → Γ → Finset (Q × List Γ) -- transition function

open PDA
variable {Sigma : Type}[Alphabet Sigma]
variable (P : PDA Sigma)

inductive Γ₀ : Type
| hash | one -- a
deriving Fintype,DecidableEq
open Γ₀

abbrev P₁ : PDA SigmaABC
:= {
  Q := Fin 3
  Γ := Γ₀
  s := 0
  z₀ := Γ₀.hash -- #
  F := { 2 }
  δ q x γ :=
    match q, x, γ with
    | 0, some a, z => {(0, [one,z])}
    | 0, some b, one => {(1, [])}
    | 0, none, Γ₀.hash => {(2,[])}
    | 1, some b, one => {(1,[])}
    | 1, none, Γ₀.hash => {(2,[])}
    | _,_,_ => {}
}

abbrev ID : Type := P.Q × Word Sigma × List P.Γ
-- instantaneous description

inductive Step : (ID P × ID P) → Prop
| read : ∀ q q' α x w z y ,
    (q' , α ) ∈ P.δ q (some x) z
    → Step ((q, x::w, z::y), (q', w, α ++ y))
| silent : ∀ q q' α w z y ,
    (q', α) ∈ P.δ q none z
    → Step ((q, w, z::y), (q', w, α ++ y))

inductive Star {A : Type}(R : A × A → Prop) : A × A → Prop
| refl : ∀ a, Star R (a, a)
| step : ∀ a b c, R (a, b) → Star R (b, c) → Star R (a,c)
-- This is the transitive, reflexive closure of a relation
-- I.e., the relation you get when you allow 0 or multiple
-- applications of R (steps in the process of an automaton,
-- or derivations within a CFG).

/-
Explicitly, Star (Step P) is this:
inductive StepStar : (ID P × ID P) → Prop
| refl : ∀ a , StepStar (a , a)
| step : ∀ a b c , Step P (a , b)
      → StepStar (b , c) → StepStar (a , c)
-/

-- Acceptance by ending in a final state
abbrev L : Lang Sigma
:= { w | ∃ q' γ ,
    Star (Step P) ((P.s,w,[P.z₀]),(q',[],γ))
                  ∧ q' ∈ P.F }

-- Acceptance by clearing the stack upon finishing the word
abbrev L_empty : Lang Sigma
 := { w | ∃ q' ,
      Star (Step P) ((P.s,w,[P.z₀]),(q',[],[])) }

-- These two ways of defining a language are equivalent in
-- the sense that there exist ways to translate a PDA
-- using L into one using L_empty while accepting the same
-- language.

-- We prove these examples by explicitly walking through the
-- parsing process of the PDA.
example : [a,a,b,b] ∈ L P₁ := by
  simp
  exists []
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.silent
  constructor
  apply Star.refl

example : [a,a,b,b] ∈ L_empty P₁ := by
  simp
  exists 2
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.read
  constructor
  apply Star.step
  apply Step.silent
  constructor
  apply Star.refl

end pda
