import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq
--import Proofs.Kleene  -- or whatever path your Kleene.lean has
--open Kleene

-- ·  ⋅
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace Lang

section Basic

local notation "Σ" => Sigma

-- ANCHOR: Alphabet
class Alphabet (Sigma : Type) : Type where
  (fintype : Fintype Sigma)
  (decEq   : DecidableEq Sigma)
-- ANCHOR_END: Alphabet

attribute [instance] Alphabet.fintype Alphabet.decEq

instance (Sigma : Type) [Fintype Sigma] [DecidableEq Sigma] : Alphabet Sigma :=
  ⟨inferInstance, inferInstance⟩

-- ANCHOR: Sigma
variable (Sigma : Type)[Alphabet Sigma]
-- ANCHOR_END: Sigma

-- ANCHOR: Word
abbrev Word := List Sigma
-- ANCHOR_END: Word

-- ANCHOR: Lang
abbrev Lang : Type :=  Set (Word Sigma)
-- ANCHOR_END: Lang

instance : HPow Sigma ℕ (Word Sigma)
where hPow := λ x n ↦ List.replicate n x

end Basic

namespace Examples

variable (Sigma : Type)[Alphabet Sigma]
-- ANCHOR: SigmaABC
inductive SigmaABC : Type
| a | b | c
-- ANCHOR_END: SigmaABC
deriving Fintype, DecidableEq
--deriving Fintype, DecidableEq, Repr
open SigmaABC

instance : Repr SigmaABC where
  reprPrec x _ :=
    match x with
    | a => "a"
    | b => "b"
    | c => "c"

example : Alphabet SigmaABC := by
  infer_instance

-- ANCHOR: SigmaBin
abbrev SigmaBin : Type
:= Fin 2
-- ANCHOR_END: SigmaBin

example : Alphabet SigmaBin := by
  infer_instance

-- example : Alphabet Char := by
--   infer_instance

axiom char_fin : Fintype Char

noncomputable example : Alphabet Char :=
{ fintype := char_fin
, decEq  := inferInstance
}


-- example : Alphabet SigmaChar := by
--   sorry

#check ([a,b] : Word SigmaABC)
#check (a^3 : Word SigmaABC)
#eval (a^3 ++ b^3 : Word SigmaABC)
#eval ([a,a,b,c].count a)
#eval (List.count a [a,a,b,c])

-- ANCHOR: aeqb
abbrev aeqb : Lang SigmaABC
:= { w : Word SigmaABC | w.count a = w.count b}
-- ANCHOR_END: aeqb

namespace aeqb_pred
-- ANCHOR: aeqb_pred
abbrev aeqb : Lang SigmaABC
| w => w.count a = w.count b
-- ANCHOR_END: aeqb_pred
end aeqb_pred

-- ANCHOR: aeqb_ex
example : [a,b] ∈ aeqb := by simp
example : [a,a,b,c] ∉ aeqb := by simp
-- ANCHOR_END: aeqb_ex
example : [] ∈ aeqb := by simp
example : [a,a,a,b] ∉ aeqb := by simp

variable (L : Lang Sigma)
variable (w : Word Sigma)

#check (w ∈ L)
#check (L w)

abbrev aeqbmod2 : Lang SigmaABC
:= { w : Word SigmaABC |
    w.count a ≡ w.count b [MOD 2]}
-- \== ≡ congruent
attribute [simp] Nat.ModEq

example : [a,b] ∈ aeqbmod2 := by simp
example : [a,a,b,c] ∉ aeqbmod2 := by simp
example : [] ∈ aeqbmod2 := by simp
example : [a,a,a,b] ∈  aeqbmod2 := by simp

-- ANCHOR: anbm
abbrev anbm : Lang SigmaABC
:= { a^n ++ b^m | (n : ℕ)(m : ℕ)}
-- ANCHOR_END: anbm

abbrev anbn : Lang SigmaABC
:= { a^n ++ b^n | (n : ℕ)}


example : [a,a,b] ∈ anbm := by
  use 2 , 1
  rfl

example : [b,a,a] ∉ anbm := by sorry

-- ANCHOR: val
def val : Word SigmaBin → ℕ
| []       => 0
| (x :: xs) => x + 2 * val xs
-- ANCHOR_END: val
-- this is little endian

#eval val [0, 1, 1]  -- Output: 6

#eval val [1, 0, 1]

-- ANCHOR: div3
abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}
-- ANCHOR_END: div3

example : [0, 1, 1] ∈ div3 :=
    by simp  [val,Nat.ModEq];

example : [1, 0, 1] ∉ div3 :=
    by simp  [val,Nat.ModEq];


#check ({[a],[a,a],[a,a,a]}: Finset (Word SigmaABC))

#eval ({1,2,2,3} = ({3,2,1} : Finset ℕ))
-- ANCHOR: a3
def a3 : Lang SigmaABC
:= {[a],[a,a],[a,a,a]}
-- ANCHOR_END: a3

namespace a3_pred

-- ANCHOR: a3_pred
def a3 : Lang SigmaABC
| w => w=[a] ∨ w=[a,a] ∨ w=[a,a,a]
-- ANCHOR_END: a3_pred

end a3_pred

end Examples

section LangOps

variable {Sigma : Type}[Alphabet Sigma]

abbrev concat (L₁ L₂ : Lang Sigma) : Lang Sigma
:= { w ++ v | (w ∈ L₁)(v ∈ L₂) }

def ε : Lang Sigma := { [] }

@[simp] lemma ε_def :
-- ANCHOR: epsilon_def
ε = { ([] : Word Sigma) }
-- ANCHOR_END: epsilon_def
:= rfl

infix:70 " ⋅ " => concat

variable (L₁ L₂ : Lang Sigma)
example :
-- ANCHOR: concat_def
L₁ ⋅ L₂ = { w ++ v | (w ∈ L₁)(v ∈ L₂) }
-- ANCHOR_END: concat_def
:= by rfl

-- ANCHOR: concat_pred
def L₃ : Lang Sigma
| x => ∃ w v : Word Sigma ,
        w ∈ L₁ ∧ v ∈ L₂ ∧ x = w ++ v
-- ANCHOR_END: concat_pred

open Nat

instance : HPow (Lang Sigma) ℕ (Lang Sigma) where
  hPow := lpow
where
  lpow : Lang Sigma → ℕ → Lang Sigma
  | _, 0     => ε
  | L, n+1   => L ⋅ lpow L n


variable (L : Lang Sigma)
variable (n : ℕ)

@[simp] lemma lpow_zero :
-- ANCHOR: lpow_zero
L ^ 0 = ε
-- ANCHOR_END: lpow_zero
:= by rfl
@[simp] lemma lpow_succ :
-- ANCHOR: lpow_succ
L ^ (n + 1) = L ⋅ (L ^ n)
-- ANCHOR_END: lpow_succ
:= by rfl
-- @[simp] lemma pow_zero (L : Lang Sigma) : L^0 = ε := rfl
-- @[simp] lemma pow_one (L : Lang Sigma) : L^1 = L := by
--   simp [pow_succ]


def star (L : Lang Sigma) : Lang Sigma
:= { w : Word Sigma | ∃ n : ℕ, (w ∈  L ^ n) }

postfix:100 " * " => star

@[simp] lemma star_def :
-- ANCHOR: star_def
L * = { w : Word Sigma | ∃ n : ℕ, (w ∈  L ^ n) }
-- ANCHOR_END: star_def
:= by rfl



end LangOps

namespace LangOpsEx
variable (Sigma : Type)[Alphabet Sigma]

open Examples
open SigmaABC

namespace UnionEx
variable (L₁ L₂ : Lang Sigma)

#check (∅ : Lang Sigma)
#check (L₁ ∪ L₂ : Lang Sigma)

-- ANCHOR: union_pred
abbrev L₁₂ : Lang Sigma
| w => w ∈ L₁ ∨ w ∈ L₂
abbrev L₀ : Lang Sigma
| _ => False
-- ANCHOR_END: union_pred


end UnionEx

-- ANCHOR: l1l2
abbrev L₁ : Lang SigmaABC
:= { [a] , [a,a] , [a,a,a] }
abbrev L₂ : Lang SigmaABC
:= { [a] , [b,c] }
-- ANCHOR_END: l1l2

example :
-- ANCHOR: l1ul2
L₁ ∪ L₂ = { [a]  , [a,a] , [a,a,a] , [b,c]}
-- ANCHOR_END: l1ul2
:= by aesop

example :
-- ANCHOR: l1dotl2
  L₁ ⋅ L₂ =
    { [a,a], [a,b,c], [a,a,a], [a,a,b,c],
      [a,a,a,a], [a,a,a,b,c] }
-- ANCHOR_END: l1dotl2
:= by aesop

-- Powers of L₂ = { [a], [b,c] }



example : L₂ ^ 0 = ({ [] } : Lang SigmaABC) := by
  rfl

example : L₂ ⋅ { [] } = { [a], [b,c] } := by
  aesop

-- variable (L : Lang Sigma)
-- variable (n : ℕ)

-- @[simp] lemma lpow_zero : L ^ 0 = ε := by rfl
-- @[simp] lemma lpow_succ : L ^ (n + 1) = L ⋅ (L ^ n) := by rfl

-- example : L₂ ^ 1 = { [a], [b,c] } := by
--   -- rewrite ^1 using simp, then aesop can finish
--   simp [L₂,lpow_succ]
--   aesop

example : L₂ ^ 1 = { [a], [b,c] } := by
  aesop

example :
-- ANCHOR: l2pow2
  L₂ ^ 2 =
    { [a,a], [a,b,c], [b,c,a], [b,c,b,c] }
-- ANCHOR_END: l2pow2
      := by aesop

example :
-- ANCHOR: l2pow3
  L₂ ^ 3 =
    { [a,a,a], [a,a,b,c], [a,b,c,a],
      [a,b,c,b,c], [b,c,a,a], [b,c,a,b,c],
      [b,c,b,c,a], [b,c,b,c,b,c] }
-- ANCHOR_END: l2pow3
      := by aesop

example :
-- ANCHOR: l2starex
  [a,b,c,a,a,b,c] ∈ L₂ *
-- ANCHOR_END: l2starex
:= by
use 5
aesop

end LangOpsEx

namespace KleeneAlg

variable {Sigma : Type}[Alphabet Sigma]


variable (L K M : Lang Sigma)

------------------------------------------------------------------------
-- Additive structure: (Lang Sigma, ∪, ∅) is a commutative idempotent monoid
------------------------------------------------------------------------

lemma union_assoc :
-- ANCHOR: union_assoc
  (L ∪ K) ∪ M = L ∪ (K ∪ M)
-- ANCHOR_END: union_assoc
:= by
  ext w
  simp [or_assoc]

lemma union_comm :
-- ANCHOR: union_comm
  L ∪ K = K ∪ L
-- ANCHOR_END: union_comm
:= by
  ext w
  simp [or_comm]

lemma union_idem :
-- ANCHOR: union_idem
  L ∪ L = L
-- ANCHOR_END: union_idem
:= by
  ext w
  simp

lemma union_empty_left :
-- ANCHOR: union_empty_left
  (∅ : Lang Sigma) ∪ L = L
-- ANCHOR_END: union_empty_left
:= by
  ext w
  simp

lemma union_empty_right :
-- ANCHOR: union_empty_right
  L ∪ (∅ : Lang Sigma) = L
-- ANCHOR_END: union_empty_right
:= by
  ext w
  simp

------------------------------------------------------------------------
-- Multiplicative structure: (Lang Sigma, ⋅, ε) is a monoid
------------------------------------------------------------------------

@[simp] lemma mem_concat {L K : Lang Sigma} {x : Word Sigma} :
  x ∈ (L ⋅ K) ↔ ∃ w v, w ∈ L ∧ v ∈ K ∧ w ++ v = x := by
  simp

lemma concat_assoc :
-- ANCHOR: concat_assoc
  (L ⋅ K) ⋅ M = L ⋅ (K ⋅ M)
-- ANCHOR_END: concat_assoc
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := L ⋅ K) (K := M) (x := x)).1 hx with ⟨wk, m, hwk, hm, rfl⟩
    rcases (mem_concat (L := L) (K := K) (x := wk)).1 hwk with ⟨w, k, hw, hk, rfl⟩
    refine (mem_concat (L := L) (K := K ⋅ M) (x := (w ++ k) ++ m)).2 ?_
    refine ⟨w, k ++ m, hw, ?_, ?_⟩
    · exact (mem_concat (L := K) (K := M) (x := k ++ m)).2 ⟨k, m, hk, hm, rfl⟩
    · simp [List.append_assoc]
  · intro hx
    rcases (mem_concat (L := L) (K := K ⋅ M) (x := x)).1 hx with ⟨w, km, hw, hkm, rfl⟩
    rcases (mem_concat (L := K) (K := M) (x := km)).1 hkm with ⟨k, m, hk, hm, rfl⟩
    refine (mem_concat (L := L ⋅ K) (K := M) (x := w ++ (k ++ m))).2 ?_
    refine ⟨w ++ k, m, ?_, hm, ?_⟩
    · exact (mem_concat (L := L) (K := K) (x := w ++ k)).2 ⟨w, k, hw, hk, rfl⟩
    · simp [List.append_assoc]

lemma concat_eps_left :
-- ANCHOR: concat_eps_left
  (ε : Lang Sigma) ⋅ L = L
-- ANCHOR_END: concat_eps_left
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := (ε : Lang Sigma)) (K := L) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
    have : w = [] := by simpa [ε] using hw
    subst this
    simpa using hv
  · intro hx
    exact (mem_concat (L := (ε : Lang Sigma)) (K := L) (x := x)).2
      ⟨[], x, by simp [ε], hx, by simp⟩

lemma concat_eps_right :
-- ANCHOR: concat_eps_right
  L ⋅ (ε : Lang Sigma) = L
-- ANCHOR_END: concat_eps_right
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := L) (K := (ε : Lang Sigma)) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
    have : v = [] := by simpa [ε] using hv
    subst this
    simpa using hw
  · intro hx
    exact (mem_concat (L := L) (K := (ε : Lang Sigma)) (x := x)).2
      ⟨x, [], hx, by simp [ε], by simp⟩


------------------------------------------------------------------------
-- Distributivity: concatenation distributes over union
------------------------------------------------------------------------

lemma concat_union_left :
-- ANCHOR: concat_union_left
  (L ∪ K) ⋅ M = (L ⋅ M) ∪ (K ⋅ M)
-- ANCHOR_END: concat_union_left
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := L ∪ K) (K := M) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
    rcases hw with hw | hw
    · left
      exact (mem_concat (L := L) (K := M) (x := w ++ v)).2 ⟨w, v, hw, hv, rfl⟩
    · right
      exact (mem_concat (L := K) (K := M) (x := w ++ v)).2 ⟨w, v, hw, hv, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases (mem_concat (L := L) (K := M) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
      exact (mem_concat (L := L ∪ K) (K := M) (x := w ++ v)).2 ⟨w, v, Or.inl hw, hv, rfl⟩
    · rcases (mem_concat (L := K) (K := M) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
      exact (mem_concat (L := L ∪ K) (K := M) (x := w ++ v)).2 ⟨w, v, Or.inr hw, hv, rfl⟩

lemma concat_union_right :
-- ANCHOR: concat_union_right
  L ⋅ (K ∪ M) = (L ⋅ K) ∪ (L ⋅ M)
-- ANCHOR_END: concat_union_right
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := L) (K := K ∪ M) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
    rcases hv with hv | hv
    · left
      exact (mem_concat (L := L) (K := K) (x := w ++ v)).2 ⟨w, v, hw, hv, rfl⟩
    · right
      exact (mem_concat (L := L) (K := M) (x := w ++ v)).2 ⟨w, v, hw, hv, rfl⟩
  · intro hx
    rcases hx with hx | hx
    · rcases (mem_concat (L := L) (K := K) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
      exact (mem_concat (L := L) (K := K ∪ M) (x := w ++ v)).2 ⟨w, v, hw, Or.inl hv, rfl⟩
    · rcases (mem_concat (L := L) (K := M) (x := x)).1 hx with ⟨w, v, hw, hv, rfl⟩
      exact (mem_concat (L := L) (K := K ∪ M) (x := w ++ v)).2 ⟨w, v, hw, Or.inr hv, rfl⟩

------------------------------------------------------------------------
-- Zero annihilates multiplication: ∅ is absorbing for concatenation
------------------------------------------------------------------------

lemma concat_empty_left :
-- ANCHOR: concat_empty_left
  (∅ : Lang Sigma) ⋅ L = (∅ : Lang Sigma)
-- ANCHOR_END: concat_empty_left
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := (∅ : Lang Sigma)) (K := L) (x := x)).1 hx with ⟨w, v, hw, -, -⟩
    simpa using hw
  · intro hx
    simpa using hx

lemma concat_empty_right :
-- ANCHOR: concat_empty_right
  L ⋅ (∅ : Lang Sigma) = (∅ : Lang Sigma)
-- ANCHOR_END: concat_empty_right
:= by
  ext x
  constructor
  · intro hx
    rcases (mem_concat (L := L) (K := (∅ : Lang Sigma)) (x := x)).1 hx with ⟨w, v, -, hv, -⟩
    simpa using hv
  · intro hx
    simpa using hx

lemma star_closed (L : Lang Sigma) :
-- ANCHOR: star_closed
  (ε : Lang Sigma) ∪ (L ⋅ (L *)) ⊆ (L *)
-- ANCHOR_END: star_closed
:= by
  intro x hx
  rcases hx with hx | hx
  · -- x ∈ ε, hence x = []
    have : x = [] := by simpa [ε] using hx
    subst this
    -- [] ∈ L* via n = 0
    rw [star_def]
    use 0
    simp
  · -- x ∈ L ⋅ L*
    rcases (mem_concat (L := L) (K := (L *)) (x := x)).1 hx with
      ⟨w, v, hwL, hvStar, rfl⟩
    rcases (by simpa [star_def] using hvStar : ∃ n, v ∈ L ^ n) with ⟨n, hvn⟩
    -- show w ++ v ∈ L* via exponent n+1
    rw [star_def]
    use (n + 1)
    simp
    use w
    constructor
    assumption
    use v

/-- Leastness: L★ is the smallest X with ε ∪ L⋅X ⊆ X. -/
lemma star_least {X : Lang Sigma}
-- ANCHOR: star_least
  (h : (ε : Lang Sigma) ∪ (L ⋅ X) ⊆ X) :
  L * ⊆ X
-- ANCHOR_END: star_least
:= by
  sorry



end KleeneAlg

end Lang
