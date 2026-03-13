import Proofs.Lang
import Proofs.CFG
import Proofs.Autom

namespace Pda
open Lang

variable (Sigma : Type)[Alphabet Sigma]

structure PDA : Type 1 where
  Q : Type -- states
  [alphQ : Alphabet Q]
  Γ : Type -- Stack alphabet
  [alphΓ : Alphabet Γ]
  s : Q    -- initial state
  Z₀ : Γ    -- initial stack
  F : Finset Q -- set of final states
  δ : Q → Option Sigma → Γ → Finset (Q × List Γ)

open PDA

variable {Sigma : Type}[Alphabet Sigma]
variable (P : PDA Sigma)

abbrev ID : Type := P.Q × Word Sigma × List P.Γ
-- Instantanous Description

inductive Step : (ID P × ID P ) → Prop
| read : ∀ q q' α x w z γ ,
    (q' , α ) ∈ P.δ q (some x) z →
       Step ((q , x :: w, z :: γ) , (q' , w , α ++ γ ) )
| silent : ∀ q q' α w z γ ,
    (q' , α ) ∈ P.δ q none z →
       Step ((q , w , z :: γ) , (q' , w , α ++ γ ) )

inductive Star {A : Type}(R : A × A → Prop)
    : A × A → Prop
| refl : ∀ a , Star R (a , a)
| step : ∀ a b c , R (a , b)
      → Star R (b , c) → Star R (a , c)
-- transitive, reflexive closure

abbrev L : Lang Sigma
:= { w | ∃ q' γ ,
    Star (Step P) ((P.s,w,[P.Z₀]),(q',[],γ))
                  ∧ q' ∈ P.F }

abbrev L_empty : Lang Sigma
 := { w | ∃ q' ,
      Star (Step P) ((P.s,w,[P.Z₀]),(q',[],[])) }

abbrev isDet : Prop
:=  ∀ q x z ,
    Fintype.card (P.δ q (some x) z) + Fintype.card (P.δ q none z) ≤ 1


end Pda

namespace PdaEx

open Pda
open Lang
open Examples

inductive Γ₁ : Type
| hash | one -- a
deriving Fintype, DecidableEq
open Γ₁

open SigmaABC
open Option

abbrev P₁ : PDA SigmaABC
:= { Q := Fin 3
     Γ := Γ₁
     s := 0
     Z₀ := hash
     F := { 2 }
     δ q x γ :=
       match q , x , γ with
        | 0 , some a , z  =>
            { ( 0 , [one , z ]) }
        | 0 , some b , Γ₁.one    =>
            { (1 , []) }
        | 1 , some b , one => { ( 1 , [])}
        | 1 , none , Γ₁.hash => { ( 2 , [] )}
        | _ , _ , _ => {} }


end PdaEx

namespace CfgPda
open Pda
open Lang
open Cfg
open Sum

variable {Sigma : Type}[Alphabet Sigma]

variable (G : CFG Sigma)

abbrev cfg2pda : PDA Sigma :=
{ Q := Fin 1
  Γ := G.NT ⊕ Sigma
  s := (0 : Fin 1)
  Z₀ := inl G.S
  δ := fun q x z =>
    match x, z with
    | none, inl A =>
        (⟪ p ∈ G.P | p.1 = A ⟫).biUnion
          (fun p => { ((0 : Fin 1), p.2) })
    | some x, inr y =>
        if h : x = y then
          { ((0 : Fin 1), ([] : List (G.NT ⊕ Sigma))) }
        else
          {}
    | _, _ => {}
  F := {}   -- acceptance by empty stack
}

end CfgPda
-- abbrev cfg2pda : PDA Sigma
-- := { Q := Fin 1
--      Γ := G.NT ⊕ Sigma
--      s := 0
--      Z₀ := inl G.S
--      δ q x z := match x , z with
--                 | none , inl A =>
--                    { (0 , α) | (A , α ) ∈ G.P  }
--                 | some x, inr y =>
--                    { (0 , []) | x = y }
--                 | _,_ => {}
--      F := {} -- acceptance by empty stack
-- }
