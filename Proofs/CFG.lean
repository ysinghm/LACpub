import Proofs.Lang

namespace Cfg
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure CFG : Type 1 where
  NT : Type
  [ alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma ))

open CFG
open Sum

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

abbrev Symbol : Type
  := G.NT ⊕ Sigma

scoped instance : Coe G.NT (Symbol G) :=
  ⟨Sum.inl⟩

scoped instance : Coe Sigma (Symbol G) :=
  ⟨Sum.inr⟩

abbrev Sent : Type
  := Word (Symbol G)

abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) | ∃ α₁ α₂ ,
      ∃ A , α = α₁ ++ [inl A] ++ α₂
      ∧ ∃ γ , (A , γ) ∈ G.P
      ∧ β = α₁ ++ γ ++ α₂ }

-- infixr:70 " ⟹ " => Deriv

inductive DerivStar : Sent G × Sent G → Prop
| refl : ∀ α , DerivStar (α , α)
| step : ∀ α β γ ,
    Deriv G (α , β) → DerivStar (β , γ)
    → DerivStar (α , γ)

abbrev emb : Word Sigma → Sent G
:= List.map inr

abbrev L : Lang Sigma
:= { w | DerivStar G ([inl G.S],emb G w)}


end Cfg



namespace CfgEx
open Lang
open Cfg
open Sum
open scoped Cfg.CFG

inductive SigmaA : Type
| lpar | rpar | a | plus | times
deriving Fintype, DecidableEq
open SigmaA

namespace Ga
inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq
open NTA

abbrev E : NTA ⊕ SigmaA := inl (NTA.E)
abbrev T : NTA ⊕ SigmaA := inl (NTA.T)
abbrev F : NTA ⊕ SigmaA := inl (NTA.F)
abbrev lpar : NTA ⊕ SigmaA := inr SigmaA.lpar
abbrev rpar : NTA ⊕ SigmaA := inr SigmaA.rpar
abbrev a : NTA ⊕ SigmaA := inr SigmaA.a
abbrev plus : NTA ⊕ SigmaA := inr SigmaA.plus
abbrev times : NTA ⊕ SigmaA := inr SigmaA.times

abbrev GA : CFG SigmaA :=
{ NT := NTA
  S := NTA.E
  P := { (NTA.E, [T]),
         (NTA.E , [E,plus,T]),
         (NTA.T, [F]),
         (NTA.T , [E,times,T]),
         (NTA.F, [a]),
         (NTA.F, [lpar,E,rpar])}
   }

end Ga

namespace Gaa

inductive NTAA : Type
| E
deriving Fintype, DecidableEq

open NTAA
open SigmaA
open Sum

abbrev GAA : CFG SigmaA :=
{ NT := NTAA
  S := E
  P := { (E, [inl E,inr plus,inl E]),
         (E, [inl E,inr times,inl E]),
         (E, [inr a]),
         (E, [inr lpar,inl E,inr rpar])}
}

end Gaa
end CfgEx

namespace ParseTrees

open Lang
open Cfg

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

open Sum

mutual

  inductive PT : G.NT → Type where
  | node : ∀ {A} , ∀ {α} ,
            (A , α ) ∈ G.P
            → PTSent α → PT A

  inductive PTSent : Sent G → Type where
  | nil : PTSent []
  | NT : ∀ {A α }, PT A → PTSent α → PTSent (inl A :: α)
  | T : ∀ a {α} , PTSent α →  PTSent (inr a :: α)

end

mutual
  def yield {A : G.NT} : PT G A → Word Sigma
  | PT.node _ pα => yieldSent pα

  def yieldSent {α : Sent G} : PTSent G α → Word Sigma
  | PTSent.nil => []
  | PTSent.NT pA pα  => yield pA ++ yieldSent pα
  | PTSent.T a pα => a :: yieldSent pα

end

abbrev L_tree : Lang Sigma
:= { w | ∃ p : PT G G.S , w = yield G p }

theorem L_tree_ok : L_tree G = Cfg.L G := by sorry

-- abbrev Amb : Prop
-- := ∃ p p' : PT G G.S ,
--           yield G p = yield G p'
--           ∧ p ≠ p'

abbrev Amb : Prop :=
  ∃ (w : Word Sigma ) (A : G.NT) (t₁ t₂ : PT G A),
    yield G t₁ = w ∧
    yield G t₂ = w ∧
    t₁ ≠ t₂

end ParseTrees

namespace ParseTreeEx

open CfgEx.Gaa
open ParseTrees
open CfgEx
open SigmaA
open Sum

abbrev p1 : PT GAA NTAA.E :=
by
  refine
    PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr plus, inl NTAA.E])
      (by simp [GAA])
      ?_
  -- RHS: E plus E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) plus ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr times, inl NTAA.E])
        (by simp [GAA])
        ?_)
      (PTSent.nil (G := GAA))
  -- RHS: E times E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) times ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))

lemma p1_yield : yield GAA p1 = [a,plus,a,times,a] := by rfl

abbrev p2 : PT GAA NTAA.E :=
by
  refine
    PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr times, inl NTAA.E])
      (by simp [GAA])
      ?_
  -- RHS: E times E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inl NTAA.E, inr plus, inl NTAA.E])
        (by simp [GAA])
        ?_)
      ?_
  -- left: E plus E
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      ?_
  refine PTSent.T (G := GAA) plus ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))
  -- then `times` and the right `a`
  refine PTSent.T (G := GAA) times ?_
  refine
    PTSent.NT (G := GAA)
      (PT.node (G := GAA) (A := NTAA.E) (α := [inr a])
        (by simp [GAA])
        (PTSent.T (G := GAA) a (PTSent.nil (G := GAA))))
      (PTSent.nil (G := GAA))

lemma p2_yield : yield GAA p1 = [a,plus,a,times,a] := by rfl

def rootOp : PT GAA NTAA.E → Option SigmaA
| PT.node (A := _) (α := α) _ _ =>
    match α with
    | [Sum.inl _, Sum.inr op, Sum.inl _] => some op
    | _ => none

lemma p1p2 : (p1 : PT GAA NTAA.E) ≠ (p2 : PT GAA NTAA.E) := by
  intro h
  have : rootOp p1 = rootOp p2 := by
    simp [h]
  -- but the root operators differ:
  -- `p1` is rooted at `plus`, `p2` is rooted at `times`.
  -- So we get `some plus = some times`, contradiction.
  simpa [p1, p2, rootOp, GAA] using this

theorem amb_gaa : Amb GAA := by
  refine ⟨[a,plus,a,times,a], NTAA.E, p1, p2, ?_, ?_, ?_⟩
  . rfl
  . rfl
  . apply p1p2

end ParseTreeEx
