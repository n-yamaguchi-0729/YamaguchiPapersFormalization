/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitDiagram
import Nyll.SchemeTheory.FiniteEtale.InverseLimitHom
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Actual eventual morphism descent between different original stages

A common refinement first brings two objects to the same original stage.
The existing scheme morphism-descent theorem then descends their morphism.
The proved pullback coherence returns it to the exact transition objects used
by the automorphism assembly theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.InverseLimitDiagram

universe u v w

private theorem transported_refinement_factorization
    {C : Type v} [Category.{w} C] {X Y U V U' V' A B : C}
    (e₀ : X ≅ U) (f₀ : Y ≅ V) (e₁ : X ≅ U') (f₁ : Y ≅ V')
    (p : U ≅ A) (q : V ≅ B) (r : U' ≅ A) (t : V' ≅ B)
    (a : X ⟶ Y) (b : A ⟶ B)
    (he : e₁.hom ≫ r.hom = e₀.hom ≫ p.hom)
    (hf : f₁.hom ≫ t.hom = f₀.hom ≫ q.hom)
    (hb : p.hom ≫ b = (e₀.inv ≫ a ≫ f₀.hom) ≫ q.hom) :
    a = e₁.hom ≫ (r.hom ≫ b ≫ t.inv) ≫ f₁.inv := by
  symm
  calc
    e₁.hom ≫ (r.hom ≫ b ≫ t.inv) ≫ f₁.inv =
        (e₁.hom ≫ r.hom) ≫ b ≫ t.inv ≫ f₁.inv := by
      simp only [Category.assoc]
    _ = (e₀.hom ≫ p.hom) ≫ b ≫ t.inv ≫ f₁.inv := by rw [he]
    _ = e₀.hom ≫ (p.hom ≫ b) ≫ t.inv ≫ f₁.inv := by
      simp only [Category.assoc]
    _ = e₀.hom ≫ ((e₀.inv ≫ a ≫ f₀.hom) ≫ q.hom) ≫ t.inv ≫ f₁.inv := by
      rw [hb]
    _ = a ≫ (f₀.hom ≫ q.hom) ≫ t.inv ≫ f₁.inv := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a ≫ (f₁.hom ≫ t.hom) ≫ t.inv ≫ f₁.inv := by rw [← hf]
    _ = a := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

variable {I : Type u} [Preorder I]
variable (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D)

/-- The component form of the actual cone composition law. -/
theorem comparison_composition_hom_app {i j k : I}
    (hij : i ≤ j) (hjk : j ≤ k) (A : stage D i) :
    (comparison D s (hij.trans hjk)).hom.app A ≫
        (toLimit D s k).map ((compositionIso D hij hjk).hom.app A) =
      (comparison D s hij).hom.app A ≫
        (comparison D s hjk).hom.app ((transition D hij).obj A) := by
  let a := (comparison D s (hij.trans hjk)).hom.app A
  let b := (toLimit D s k).map ((compositionIso D hij hjk).hom.app A)
  let c := (comparison D s hij).hom.app A
  let d := (comparison D s hjk).hom.app ((transition D hij).obj A)
  have h : a ≫ (b ≫ 𝟙 _) = c ≫ d :=
    congrArg (fun q ↦ q.hom.app A) (comparison_composition D s hij hjk)
  rw [Category.comp_id] at h
  exact h

variable [IsDirectedOrder I] [Nonempty I]
variable (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (D.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]

include hs in
/-- The actual qcqs scheme data supply the exact across-stage morphism descent
used by automorphism assembly; no comparison-map assumption is introduced. -/
theorem eventualHom
    (i j : I) (A : stage D i) (B : stage D j)
    (f : (toLimit D s i).obj A ⟶ (toLimit D s j).obj B) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
      (g : (transition D hik).obj A ⟶ (transition D hjk).obj B),
      f = (comparison D s hik).hom.app A ≫ (toLimit D s k).map g ≫
        (comparison D s hjk).inv.app B := by
  obtain ⟨k₀, hik₀, hjk₀⟩ := exists_ge_ge i j
  let A₀ : stage D k₀ := (transition D hik₀).obj A
  let B₀ : stage D k₀ := (transition D hjk₀).obj B
  let f₀ : (toLimit D s k₀).obj A₀ ⟶ (toLimit D s k₀).obj B₀ :=
    (comparison D s hik₀).inv.app A ≫ f ≫ (comparison D s hjk₀).hom.app B
  obtain ⟨k, hk, b, hb⟩ := exists_inverse_limit_stage_hom D s hs
    (Opposite.op k₀) A₀ B₀ f₀
  let h₀k : k₀ ≤ k.unop := leOfHom hk.unop
  let b' : (transition D h₀k).obj A₀ ⟶ (transition D h₀k).obj B₀ := b
  let cA := (compositionIso D hik₀ h₀k).app A
  let cB := (compositionIso D hjk₀ h₀k).app B
  let g : (transition D (hik₀.trans h₀k)).obj A ⟶
      (transition D (hjk₀.trans h₀k)).obj B := cA.hom ≫ b' ≫ cB.inv
  refine ⟨k.unop, hik₀.trans h₀k, hjk₀.trans h₀k, g, ?_⟩
  have hb' : (comparison D s h₀k).hom.app A₀ ≫ (toLimit D s k.unop).map b' =
      f₀ ≫ (comparison D s h₀k).hom.app B₀ := hb
  have hfactor := transported_refinement_factorization
    ((comparison D s hik₀).app A) ((comparison D s hjk₀).app B)
    ((comparison D s (hik₀.trans h₀k)).app A)
    ((comparison D s (hjk₀.trans h₀k)).app B)
    ((comparison D s h₀k).app A₀) ((comparison D s h₀k).app B₀)
    ((toLimit D s k.unop).mapIso cA) ((toLimit D s k.unop).mapIso cB)
    f ((toLimit D s k.unop).map b')
    (comparison_composition_hom_app D s hik₀ h₀k A)
    (comparison_composition_hom_app D s hjk₀ h₀k B) hb'
  have hg : (toLimit D s k.unop).map g =
      (toLimit D s k.unop).map cA.hom ≫
        (toLimit D s k.unop).map b' ≫ (toLimit D s k.unop).map cB.inv :=
    ((toLimit D s k.unop).map_comp cA.hom (b' ≫ cB.inv)).trans
      (congrArg (fun q ↦ (toLimit D s k.unop).map cA.hom ≫ q)
        ((toLimit D s k.unop).map_comp b' cB.inv))
  rw [hg]
  exact hfactor

end AlgebraicGeometry.FiniteEtale.InverseLimitDiagram
