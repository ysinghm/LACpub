import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Powerset
import Proofs.Lang

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace Dfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

-- ANCHOR: DFA
structure DFA : Type 1 where
  Q : Type
  [alphQ : Alphabet Q]
  s : Q
  F : Finset Q
  δ : Q → Sigma → Q
-- ANCHOR_END: DFA

variable {Sigma : Type}[Alphabet Sigma]
variable (A : DFA Sigma)

-- ANCHOR: delta_star
def δ_star : A.Q → Word Sigma → A.Q
| q , [] => q
| q , (x :: w) => δ_star (A.δ q x) w
-- ANCHOR_END: delta_star

-- ANCHOR: DFA_L
abbrev L : Lang Sigma
:= { w | δ_star A A.s w ∈ A.F}
-- ANCHOR_END: DFA_L

end Dfa

namespace DFAex

open Lang.Examples
open Dfa
open DFA
open SigmaABC

-- ANCHOR: A1
abbrev A₁ : DFA SigmaABC
:= {
  Q := Fin 2
  s := 0
  F := { 1 }
  δ := λ  | 0 , a => 1
          | 0 , _ => 0
          | 1 , _ => 1
}
-- ANCHOR_END: A1

attribute [instance] DFA.alphQ

example : [a , b] ∈ L A₁ := by aesop
example : [b , b] ∉ L A₁ := by
  dsimp [δ_star ]
  aesop

-- ANCHOR: A2
abbrev A₂ : DFA SigmaABC
:= {
  Q := Fin 3
  s := 0
  F := { 0 , 1 }
  δ := λ | 0 , a => 0
         | 0 , b => 1
         | 0 , c => 2
         | 1 , b => 1
         | 1 , _ => 2
         | 2 , _ => 2
}
-- ANCHOR_END: A2

inductive Q_oe : Type
| EE | EO | OE | OO
deriving Fintype, DecidableEq
open Q_oe

def A_oe : DFA SigmaABC :=
  {   Q := Q_oe
      s := EE
      F := {EE , OO}
      δ :=  λ | EE , a => OE
              | EE , b => EO
              | OE , a => EE
              | OE , b => OO
              | EO , a => OO
              | EO , b => EE
              | OO , a => EO
              | OO , b => OE
              | q  , c => q
 }


end DFAex

namespace Nfa
open Lang

variable (Sigma : Type)[Alphabet Sigma]

-- ANCHOR: NFA
structure NFA : Type 1 where
  Q : Type
  [alphQ : Alphabet Q]
  S : Finset Q
  F : Finset Q
  δ : Q → Sigma → Finset Q
-- ANCHOR_END: NFA

attribute [instance] NFA.alphQ

variable {Sigma : Type}[Alphabet Sigma]
variable (A : NFA Sigma)

macro "⟪" q:ident " | " P:term "⟫" : term =>
  `( (Finset.univ).filter (fun $q => $P) )
macro "⟪" q:ident " ∈ " xs:term " | " P:term "⟫" : term =>
  `( ($xs).filter (fun $q => $P) )

macro "⟪" q:ident " ∈ " xs:term " ↦ " f:term "⟫" : term =>
  `( ($xs).image
      ⟨fun $q => $f, by
        intro a b h
        cases h
        rfl⟩ )

-- ANCHOR: delta_step
def δ_step (A : NFA Sigma) (S : Finset A.Q) (a : Sigma) : Finset A.Q :=
  ⟪ q | ∃ p ∈ S, q ∈ A.δ p a ⟫
-- ANCHOR_END: delta_step

-- def δ_step (A : NFA Sigma) (S : Finset A.Q) (a : Sigma) : Finset A.Q :=
--   S.biUnion (fun q => A.δ q a)

-- ANCHOR: NFA_delta_star
def δ_star : Finset A.Q → Word Sigma → Finset A.Q
| S, []      => S
| S, a :: w  => δ_star (δ_step A S a) w
-- ANCHOR_END: NFA_delta_star

-- ANCHOR: NFA_L
abbrev L : Lang Sigma
:= { w : Word Sigma |
      ∃ q : A.Q ,
      q ∈ A.F ∩ δ_star A A.S w }
-- ANCHOR_END: NFA_L

namespace NFAex

open Lang.Examples
open NFA
open SigmaABC

def A₃ : NFA (Fin 2)
:= { Q := Fin 3
     S := { 0 }
     F := { 2 }
     δ := λ | 0 , 0 => {0}
            | 0 , 1 => {0,1}
            | 1,  _  => {2}
            | _ , _ => {}
}

example : [0,1,0] ∈ L A₃ := sorry -- by simp [A₃,L,δ_star]
example : [1,0,1] ∉ L A₃ := sorry

end NFAex

namespace nfaDfa

variable {Sigma : Type}
[Fintype Sigma][DecidableEq Sigma]

-- ANCHOR: dfa2nfa
def dfa2nfa (A : Dfa.DFA Sigma) : Nfa.NFA Sigma
:= { Q := A.Q
     S := {A.s}
     F := A.F
     δ := λ s w ↦ { A.δ s w}}
-- ANCHOR_END: dfa2nfa

open Finset

lemma dfa2nfa_δ_step_singleton (A : Dfa.DFA Sigma) (q : A.Q) (a : Sigma) :
    Nfa.δ_step (dfa2nfa (Sigma := Sigma) A) ({q} : Finset A.Q) a
      = ({A.δ q a} : Finset A.Q) := by
  -- unfold and ext; purely by simp
  ext r
  simp [Nfa.δ_step, dfa2nfa]

lemma dfa2nfa_δ_star_singleton (A : Dfa.DFA Sigma) :
    ∀ (q : A.Q) (w : Word Sigma),
      Nfa.δ_star (A := dfa2nfa (Sigma := Sigma) A) ({q} : Finset A.Q) w
        = ({Dfa.δ_star A q w} : Finset A.Q)
  | q, [] => by
      simp [Nfa.δ_star, Dfa.δ_star]
  | q, a :: w => by
      -- unfold one step, use the singleton-step lemma, then IH
      simp [Nfa.δ_star, Dfa.δ_star, dfa2nfa_δ_step_singleton, dfa2nfa_δ_star_singleton]

-- theorem dfa2nfa_ok : ∀ A : Dfa.DFA Sigma,
--     Dfa.L A = Nfa.L (dfa2nfa (Sigma := Sigma) A)

-- ANCHOR: dfa2nfa_ok
theorem dfa2nfa_ok : ∀ A : Dfa.DFA Sigma,
    Dfa.L A = Nfa.L (dfa2nfa A)
-- ANCHOR_END: dfa2nfa_ok
:= by
  intro A
  ext w
  constructor
  · intro hw
    -- show NFA accepts: pick the unique reachable state
    refine ⟨Dfa.δ_star A A.s w, ?_⟩
    -- membership in intersection
    have : Nfa.δ_star (A := dfa2nfa (Sigma := Sigma) A) ({A.s} : Finset A.Q) w
              = ({Dfa.δ_star A A.s w} : Finset A.Q) :=
      dfa2nfa_δ_star_singleton (Sigma := Sigma) A A.s w
    -- now simp it out
    -- goal: Dfa.δ_star A A.s w ∈ A.F ∩ δ_starN ...
    -- which is (∈ A.F) ∧ (∈ singleton ...)
    --
    -- simpa [Nfa.L, Dfa.L, this, Finset.mem_inter] using And.intro hw (by simp)
    have hF : Dfa.δ_star A A.s w ∈ A.F := hw
    have hS :
        Dfa.δ_star A A.s w ∈
          Nfa.δ_star (A := dfa2nfa (Sigma := Sigma) A) ({A.s} : Finset A.Q) w := by
      -- use your singleton-star lemma (call it `this` if you already have it)
      -- this : Nfa.δ_star ... {A.s} w = {Dfa.δ_star A A.s w}
      -- then membership is by simp
      simpa [this]
    exact (Finset.mem_inter).2 ⟨hF, hS⟩
  · intro hw
    rcases hw with ⟨q, hq⟩
    have hstar :
        Nfa.δ_star (A := dfa2nfa (Sigma := Sigma) A) ({A.s} : Finset A.Q) w
          = ({Dfa.δ_star A A.s w} : Finset A.Q) :=
      dfa2nfa_δ_star_singleton (Sigma := Sigma) A A.s w
    -- split intersection membership once
    have hqF : q ∈ A.F := (Finset.mem_inter.mp hq).1
    have hqS :
        q ∈ Nfa.δ_star (A := dfa2nfa (Sigma := Sigma) A) ({A.s} : Finset A.Q) w :=
      (Finset.mem_inter.mp hq).2
    -- from hqS and hstar, q must be the unique element Dfa.δ_star ...
    have hqEq : q = Dfa.δ_star A A.s w := by
      apply Finset.mem_singleton.mp
      -- rewrite hqS along hstar
      simpa [hstar] using hqS
    -- conclude DFA acceptance
    simpa [Dfa.L, hqEq] using hqF

-- Enumerate all finsets over a finite type by powerset of univ
instance instFintypeFinset (α : Type) [Fintype α] [DecidableEq α] : Fintype (Finset α) where
  elems := (Finset.univ : Finset α).powerset
  complete := by
    intro s
    -- mem_powerset : s ∈ t.powerset ↔ s ⊆ t
    simpa [Finset.mem_powerset] using (Finset.subset_univ s)

instance instAlphabetFinset (α : Type) [Alphabet α] : Alphabet (Finset α) :=
  ⟨inferInstance, inferInstance⟩

abbrev Pow (α : Type) [Fintype α] [DecidableEq α] : Finset (Finset α) :=
  (Finset.univ : Finset α).powerset

-- ANCHOR: nfa2dfa
def nfa2dfa (A : Nfa.NFA Sigma) : Dfa.DFA Sigma
     := { Q := Finset A.Q
          s := A.S
          F := ⟪ S ∈ Pow A.Q |
                ∃ (q : A.Q) , q ∈ S ∧ q ∈ A.F ⟫
          δ := δ_step A }
-- ANCHOR_END: nfa2dfa

#check (by infer_instance : DecidableEq A.Q)
#check (by infer_instance : Fintype A.Q)

lemma nfa2dfa_δ_star (A : Nfa.NFA Sigma) :
    ∀ (S : Finset A.Q) (w : Word Sigma),
      Dfa.δ_star (A := nfa2dfa (Sigma := Sigma) A) S w
        = Nfa.δ_star (A := A) S w
  | S, [] => by
      simp [Dfa.δ_star, Nfa.δ_star, nfa2dfa]
  | S, a :: w => by
      -- unfold one step on both sides; this reduces to the IH on the new state-set
      simp [Dfa.δ_star, Nfa.δ_star, nfa2dfa]
      -- goal is now exactly the IH with S := δ_step A S a
      exact nfa2dfa_δ_star (S := Nfa.δ_step A S a) (w := w)

-- ANCHOR: nfa2dfa_ok
theorem nfa2dfa_ok :
  ∀ A : Nfa.NFA Sigma,
  Nfa.L A = Dfa.L (nfa2dfa  A)
-- ANCHOR_END: nfa2dfa_ok
:= by
  intro A
  ext w
  -- rewrite DFA δ_star to NFA δ_star
  have hstar :
      Dfa.δ_star (A := nfa2dfa (Sigma := Sigma) A) A.S w
        = Nfa.δ_star (A := A) A.S w :=
    nfa2dfa_δ_star (Sigma := Sigma) A A.S w

  constructor
  · intro hw
    -- hw : ∃ q, q ∈ A.F ∩ Nfa.δ_star A A.S w
    rcases hw with ⟨q, hq⟩
    have hqF : q ∈ A.F := (Finset.mem_inter.mp hq).1
    have hqS : q ∈ Nfa.δ_star (A := A) A.S w := (Finset.mem_inter.mp hq).2

    -- show DFA accepts: δ_star ∈ filter Pow predicate
    -- 1) membership in Pow is automatic because subset_univ
    have hPow : Nfa.δ_star (A := A) A.S w ∈ Pow A.Q := by
      -- Pow α = (univ : Finset α).powerset
      -- mem_powerset : s ∈ t.powerset ↔ s ⊆ t
      simp [Pow, Finset.mem_powerset]

    -- 2) build membership in the filtered finset of finals
    have hFinal :
        (Dfa.δ_star (A := nfa2dfa (Sigma := Sigma) A) A.S w) ∈
          (nfa2dfa (Sigma := Sigma) A).F := by
      -- rewrite δ_star using hstar
      -- then use mem_filter: x ∈ t.filter p ↔ x ∈ t ∧ p x
      -- predicate: ∃ q, q ∈ x ∧ q ∈ A.F, witnessed by our q
      have :
          (Nfa.δ_star (A := A) A.S w) ∈ (nfa2dfa (Sigma := Sigma) A).F := by
        -- unfold the definition of F in nfa2dfa
        -- (it is a filter over Pow A.Q)
        refine (Finset.mem_filter).2 ?_
        refine ⟨hPow, ?_⟩
        refine ⟨q, ?_⟩
        exact ⟨hqS, hqF⟩
      -- transport along hstar
      simpa [hstar] using this

    -- Dfa.L is exactly that membership
    simpa [Dfa.L] using hFinal

  · intro hw
    -- name the DFA to avoid it being unfolded into a record literal everywhere
    let D : Dfa.DFA Sigma := nfa2dfa (Sigma := Sigma) A

    -- hw is acceptance in the DFA language
    have hFinal :
        (Dfa.δ_star (A := D) A.S w) ∈ D.F := by
      simpa [Dfa.L, D] using hw

    -- unfold only the definition of D.F (i.e. the filter), then extract witness
    dsimp [D, nfa2dfa] at hFinal
    have hx := Finset.mem_filter.mp hFinal
    rcases hx.2 with ⟨q : A.Q, hqS_dfa, hqF⟩

    -- relate DFA δ_star to NFA δ_star (your lemma)
    have hstar :
        Dfa.δ_star (A := D) A.S w = Nfa.δ_star (A := A) A.S w :=
      nfa2dfa_δ_star (Sigma := Sigma) A A.S w

    -- transport membership along hstar
    have hqS : q ∈ Nfa.δ_star (A := A) A.S w := by
      -- hqS_dfa : q ∈ Dfa.δ_star (A := D) A.S w
      --simpa [hstar] using hqS_dfa
      sorry

    -- build NFA acceptance witness
    refine ⟨q, (Finset.mem_inter).2 ?_⟩
    exact ⟨hqF, hqS⟩

end nfaDfa

section nfaDfaEx

open Lang.Examples
open SigmaABC
open Dfa.DFA
open Nfa.NFA
open DFAex
open NFAex
open nfaDfa

#check dfa2nfa A₁

def NA₁ : NFA SigmaABC :=
-- ANCHOR: NA1
   { Q := Fin 2
     S := { 0 }
     F := { 1 }
     δ := λ | 0 , a => {1}
            | 0 , _ => {0}
            | 1,  _ => {1}
}
-- ANCHOR_END: NA1

#check nfa2dfa A₃

open Finset

def DA₃ : Dfa.DFA (Fin 2) :=
-- ANCHOR: DA3
{ Q := Finset (Fin 3)
  s := {0}
  F := { {2}, {0,2}, {1,2}, {0,1,2} }
  δ := δ_step A₃
}
-- ANCHOR_END: DA3


end nfaDfaEx
