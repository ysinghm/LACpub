import Proofs.Lang
open Lang

variable (Sigma : Type)[Alphabet Sigma]

open Sum

structure CFG : Type 1 where
  NT : Type
  [alphNT : Alphabet NT]
  S : NT
  P : Finset (NT × Word (Sum NT Sigma))


variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma )

abbrev Sent : Type -- Sentence Form
:= Word (Sum G.NT Sigma)

abbrev Deriv : Set (Sent G × Sent G)
:= { (α , β) |
      ∃ w w' : Sent G, ∃ A : G.NT, ∃ γ : Sent G,
      α = w ++ [inl A] ++ w'
      ∧ β = w ++ γ ++ w'
      ∧ (A , γ) ∈ G.P
}

inductive DerivStar : Set (Sent G × Sent G)
| refl : ∀ α , DerivStar (α,α)
| step : ∀ α β γ,
        Deriv G (α , β) → DerivStar (β, γ)
         → DerivStar (α , γ)

open Sum

abbrev emb : Word Sigma → Sent G
:= List.map inr

abbrev L : Lang Sigma
:= { w | DerivStar G ([inl G.S],emb G w)}

-- A for Arithmetic

inductive SigmaA : Type
| a | plus | times | lpar | rpar
deriving Fintype, DecidableEq
-- a , + , * , ( , )

namespace Ga

-- Fin 3
inductive NTA : Type
| E | T | F
deriving Fintype, DecidableEq

open SigmaA
open NTA
open CFG

abbrev GA : CFG SigmaA
:= { NT := NTA,
     S := E,
     P := { (E , [ inl T ]),
            (E , [ inl E , inr plus, inl T]),
            (T , [ inl F]),
            (T , [ inl T, inr times, inl F]),
            (F , [ inr a]),
            (F , [ inr lpar , inl E, inr rpar])
            }
}

/-
E -> T | E + T
T -> F | T * F
F -> a | ( E )
-/

end Ga

/-
E -> E + E | E * E | a | ( E )
-/

open SigmaA

abbrev GAA : CFG SigmaA
:= {
    NT := Fin 1
    S := 0
    P := { (0 , [inl 0,inr plus,inl 0 ]),
           (0 , [inl 0,inr times,inl 0]),
           (0 , [inr a]),
           (0 , [inr lpar,inl 0,inr rpar])
    }
}

theorem today : L Ga.GA = L GAA := by sorry

--- What is parse tree?
--- What does it mean that a grammar ambiguous ?
--- there is more than parse tree for at least one word.

variable (G : CFG Sigma)

mutual

  inductive PT : G.NT → Type

    | node : ∀ {A} , ∀ {α} , (A , α ) ∈ G.P
        → PTSent α → PT A

  inductive PTSent : Sent G → Type

    | nil  : PTSent []
    | NT : ∀ {A}, ∀ {α} ,
        PT A → PTSent α → PTSent ((inl A)::α)
    | T : ∀ a {α} , PTSent α → PTSent (inr a :: α)

end

open PT
open PTSent

variable (G : CFG Sigma)

mutual

  def yield {A : G.NT }: PT G A → Word Sigma
  | node _ t => yieldSent t

  def yieldSent {α : Sent G} : PTSent G α → Word Sigma
  | nil => []
  | NT t ts => yield t ++ yieldSent ts
  | T a ts => a :: yieldSent ts

end

abbrev Amb : Prop
:= ∃ w : Word Sigma ,
   ∃ A : G.NT , ∃ t t' : PT G A , yield G t = w ∧ yield G t' = w
   ∧ t ≠ t'
