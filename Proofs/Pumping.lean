--import Mathlib.Logic.Basic
import Mathlib.Tactic.TFAE
import Proofs.Lang
import Proofs.Autom
import Proofs.RE
--import Proofs.Kleene

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace Pumping

open Lang
--open Examples
open Nat
--open Dfa

variable (Sigma : Type)[Alphabet Sigma]

-- Set (Set (Word Sigma))
-- ANCHOR: REG
abbrev REG : Set (Lang Sigma)
:= { L | ∃ A : Dfa.DFA Sigma ,
     L = Dfa.L A}
-- ANCHOR_END: REG



variable {Sigma : Type}[Alphabet Sigma]

theorem regEquiv1 :
    ∀ L : Lang Sigma ,
    L ∈ REG Sigma ↔ (∃ A : Nfa.NFA Sigma, Nfa.L A = L) := sorry

theorem regEquiv2 :
    ∀ L : Lang Sigma ,
    L ∈ REG Sigma ↔ (∃ E : Re.RE Sigma, Re.L E = L) := sorry

-- ANCHOR: TFAE
theorem regTFAE (L : Lang Sigma) :
  List.TFAE
    [ L ∈ REG Sigma
    , ∃ A : Nfa.NFA Sigma, Nfa.L A = L
    , ∃ E : Re.RE Sigma, Re.L E = L
    ]
-- ANCHOR_END: TFAE
    :=  by
  tfae_have 1 ↔ 2 := regEquiv1 (Sigma := Sigma) L
  tfae_have 1 ↔ 3 := regEquiv2 (Sigma := Sigma) L
  tfae_finish

-- ANCHOR: pump
def pump : Word Sigma → ℕ → Word Sigma
| w , 0 => []
| w , (succ n) => w ++ pump w n
-- ANCHOR_END: pump

lemma δ_star_append (A : Dfa.DFA Sigma) :
    ∀ (q : A.Q) (u v : Word Sigma),
      Dfa.δ_star A q (u ++ v) = Dfa.δ_star A (Dfa.δ_star A q u) v
| q, [], v => by
    simp [Dfa.δ_star]
| q, a :: u, v => by
    simp [Dfa.δ_star, δ_star_append, List.cons_append]

lemma δ_star_pump_fix
    (A : Dfa.DFA Sigma) {q : A.Q} {y : Word Sigma}
    (h : Dfa.δ_star A q y = q) :
    ∀ m : ℕ, Dfa.δ_star A q (pump y m) = q
| 0 => by
    simp [pump, Dfa.δ_star]
| m+1 => by
    simp [pump, δ_star_append, h, δ_star_pump_fix A h m]

-- ANCHOR: pumping
lemma pumpingLemma : ∀ A : Dfa.DFA Sigma ,
  ∃ n : ℕ ,
  ∀ w : Word Sigma,
  w ∈ Dfa.L A → w.length ≥ n →
  ∃ x y z : Word Sigma,
  w = x ++ y ++ z ∧
  x.length + y.length ≤ n ∧
  y.length ≥ 1 ∧
  ∀ m : ℕ, x ++ (pump y m) ++ z ∈ Dfa.L A
-- ANCHOR_END: pumping
:= by
  intro A
  refine ⟨Fintype.card A.Q, ?_⟩
  intro w hwA hwlen
  classical -- unneccessary because of PHP

  let n := Fintype.card A.Q

  -- States reached after prefixes of lengths 0,...,n
  let f : Fin (n + 1) → A.Q := fun i =>
    Dfa.δ_star A A.s (w.take i.1)

  have hnotinj : ¬ Function.Injective f := by
    intro hf
    have hle := Fintype.card_le_of_injective f hf
    have hle' : n + 1 ≤ n := by
      simpa [n] using hle
    exact Nat.not_succ_le_self n hle'

  have hni : ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := by
    by_contra h
    apply hnotinj
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩

  rcases hni with ⟨i, j, hij_ne, hEq⟩

  have hij_val_ne : i.1 ≠ j.1 := by
    intro h
    apply hij_ne
    exact Fin.ext h

  have hchoice :
      ∃ i0 j0 : ℕ,
        i0 < j0 ∧
        j0 ≤ n ∧
        Dfa.δ_star A A.s (w.take i0) = Dfa.δ_star A A.s (w.take j0) := by
    by_cases hlt : i.1 < j.1
    · refine ⟨i.1, j.1, hlt, ?_, hEq⟩
      omega
    · have hgt : j.1 < i.1 := by
        omega
      refine ⟨j.1, i.1, hgt, ?_, hEq.symm⟩
      omega

  rcases hchoice with ⟨i0, j0, hij, hj0le, hEq0⟩

  have hj0w : j0 ≤ w.length := by
    exact le_trans hj0le hwlen

  have hi0w : i0 ≤ w.length := by
    omega

  let u : Word Sigma := w.take j0
  let x : Word Sigma := u.take i0
  let y : Word Sigma := u.drop i0
  let z : Word Sigma := w.drop j0

  have hu_len : u.length = j0 := by
    dsimp [u]
    simp [List.length_take, hj0w]

  have hx_def : x = w.take i0 := by
    dsimp [x, u]
    rw [List.take_take]
    simp [Nat.min_eq_left (Nat.le_of_lt hij)]

  have hxy_def : x ++ y = w.take j0 := by
    dsimp [x, y, u]
    simpa using (List.take_append_drop i0 (w.take j0))

  have hw_def : w = x ++ y ++ z := by
    calc
      w = w.take j0 ++ w.drop j0 := by
        symm
        exact List.take_append_drop j0 w
      _ = (x ++ y) ++ z := by
        simp [hxy_def, z]
      _ = x ++ y ++ z := by simp [List.append_assoc]

  have hx_len : x.length = i0 := by
    rw [hx_def]
    simp [List.length_take, hi0w]

  have hy_len : y.length = j0 - i0 := by
    dsimp [y]
    rw [List.length_drop, hu_len]

  have hxy_len : x.length + y.length ≤ n := by
    rw [hx_len, hy_len]
    omega

  have hy_pos : y.length ≥ 1 := by
    rw [hy_len]
    omega

  have hloop :
      Dfa.δ_star A (Dfa.δ_star A A.s x) y
        = Dfa.δ_star A A.s x := by
    calc
      Dfa.δ_star A (Dfa.δ_star A A.s x) y
          = Dfa.δ_star A A.s (x ++ y) := by
              symm
              exact δ_star_append A A.s x y
      _ = Dfa.δ_star A A.s (w.take j0) := by
            simp [hxy_def]
      _ = Dfa.δ_star A A.s (w.take i0) := hEq0.symm
      _ = Dfa.δ_star A A.s x := by
            simp [hx_def]

  have hz_accept :
      Dfa.δ_star A (Dfa.δ_star A A.s x) z ∈ A.F := by
    have hwA' : Dfa.δ_star A A.s (x ++ y ++ z) ∈ A.F := by
      simpa [Dfa.L, hw_def] using hwA
    simpa [List.append_assoc, δ_star_append, hloop] using hwA'

  refine ⟨x, y, z, hw_def, hxy_len, hy_pos, ?_⟩
  intro m
  have hpump :
      Dfa.δ_star A (Dfa.δ_star A A.s x) (pump y m)
        = Dfa.δ_star A A.s x :=
    δ_star_pump_fix A hloop m

  show x ++ pump y m ++ z ∈ Dfa.L A
  change Dfa.δ_star A A.s (x ++ pump y m ++ z) ∈ A.F
  simpa [List.append_assoc, δ_star_append, hpump] using hz_accept

open Examples

@[simp]
lemma length_pow (x : Sigma) (n : ℕ) :
    List.length (x ^ n : Word Sigma) = n := by
  change List.length (List.replicate n x) = n
  simp

@[simp] lemma pow_def (x : Sigma) (n : ℕ) :
  (x ^ n : Word Sigma) = List.replicate n x :=
rfl

lemma drop_a_pow (i j : ℕ) :
    List.drop i (SigmaABC.a ^ (i + j) : Word SigmaABC) = SigmaABC.a ^ j := by
  simp

lemma prefix_eq_a_pow
    (k n : ℕ) (h : k ≤ n) :
    List.take k ((SigmaABC.a ^ n : Word SigmaABC) ++ SigmaABC.b ^ n)
      = SigmaABC.a ^ k := by
  rw [List.take_append_of_le_length (by simpa using h)]
  simp [h]

-- ANCHOR: anbn_pump
lemma anbn_pump: ¬ ∃ A : Dfa.DFA SigmaABC ,
                      Dfa.L A = anbn
-- ANCHOR_END: anbn_pump
:= by
intro h
rcases h with ⟨A, hA⟩
rcases pumpingLemma (Sigma := SigmaABC) A with ⟨n, hn⟩

let w : Word SigmaABC := SigmaABC.a ^ n ++ SigmaABC.b ^ n

have hw_anbn : w ∈ anbn := by
  dsimp [w, Examples.anbn]
  use n

have hwA : w ∈ Dfa.L A := by
    rw [hA]
    exact hw_anbn

have hwlen : w.length ≥ n := by
  change (List.replicate n SigmaABC.a ++ List.replicate n SigmaABC.b).length ≥ n
  simp

rcases hn w hwA hwlen with ⟨x, y, z, hw, hxylen, hylen, hpump⟩

have hprefix :
    x ++ y = SigmaABC.a ^ (x.length + y.length) := by
  have h1 : List.take (x.length + y.length) (x ++ y ++ z) = x ++ y := by
    show List.take (x.length + y.length) ((x ++ y) ++ z) = x ++ y
    rw [List.take_append_of_le_length]
    · simp
    · simp
  have h2 :
      List.take (x.length + y.length)
        ((SigmaABC.a ^ n : Word SigmaABC) ++ SigmaABC.b ^ n)
        = SigmaABC.a ^ (x.length + y.length) := by
    apply prefix_eq_a_pow
    exact hxylen
  rw [← hw] at h1
  exact h1.symm.trans h2

have hy_a : y = SigmaABC.a ^ y.length := by
  have hdrop := congrArg (List.drop x.length) hprefix
  rw [List.drop_append] at hdrop
  simpa [drop_a_pow] using hdrop

have hxzA : x ++ z ∈ Dfa.L A := by
  have := hpump 0
  simpa [pump] using this

have hxz_anbn : x ++ z ∈ anbn := by
  rw [← hA]
  exact hxzA

rcases hxz_anbn with ⟨m, hm⟩

have hy_count_a : y.count SigmaABC.a = y.length := by
  rw [hy_a]
  simp

have hy_count_b : y.count SigmaABC.b = 0 := by
  rw [hy_a]
  simp [List.count_replicate]

have hcount_a_w : w.count SigmaABC.a = n := by
  dsimp [w]
  simp [List.count_replicate]

have hcount_b_w : w.count SigmaABC.b = n := by
  dsimp [w]
  simp [List.count_replicate]

have hypos : 0 < y.length := by
  exact hylen

have hcount_a_xyz :
    x.count SigmaABC.a + y.count SigmaABC.a + z.count SigmaABC.a = n := by
  rw [← hcount_a_w, hw]
  simp [List.count_append, Nat.add_assoc]

have hcount_b_xyz :
    x.count SigmaABC.b + y.count SigmaABC.b + z.count SigmaABC.b = n := by
  rw [← hcount_b_w, hw]
  simp [List.count_append, Nat.add_assoc]

have hcount_a_xz : (x ++ z).count SigmaABC.a + y.length = n := by
  rw [List.count_append]
  simpa [hy_count_a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcount_a_xyz

have hcount_b_xz : (x ++ z).count SigmaABC.b = n := by
  rw [List.count_append]
  simpa [hy_count_b, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcount_b_xyz

have hxz_count_a : (x ++ z).count SigmaABC.a = m := by
  rw [← hm]
  simp [List.count_replicate]

have hxz_count_b : (x ++ z).count SigmaABC.b = m := by
  rw [← hm]
  simp [List.count_replicate]

omega

-- ANCHOR: anbnNotReg
theorem anbnNotReg : anbn ∉ REG SigmaABC
-- ANCHOR_END: anbnNotReg
 := by
  intro h
  apply anbn_pump
  rcases h with ⟨A, hA⟩
  exact ⟨A, hA.symm⟩

end Pumping
