/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.InverseLimitStages
import SchemeTheory.FiniteEtale.InverseLimitHom
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Fullness of the finite étale model localization

Actual finite-étale Hom descent produces a right fraction representing each
morphism over the limiting scheme.  Fullness is a conclusion of that
geometric theorem, with the original qcqs and affine-transition inputs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u v w

private theorem iso_square_inv
    {C : Type v} [Category.{w} C] {X X' Y Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (a : X ⟶ Y) (b : X' ⟶ Y')
    (h : eX.hom ≫ b = a ≫ eY.hom) : eX.inv ≫ a = b ≫ eY.inv := by
  apply (cancel_epi eX.hom).1
  calc
    eX.hom ≫ (eX.inv ≫ a) = a := eX.hom_inv_id_assoc a
    _ = (a ≫ eY.hom) ≫ eY.inv :=
      ((Category.assoc a eY.hom eY.inv).trans
        ((congrArg (fun q ↦ a ≫ q) eY.hom_inv_id).trans (Category.comp_id a))).symm
    _ = (eX.hom ≫ b) ≫ eY.inv := congrArg (fun q ↦ q ≫ eY.inv) h.symm
    _ = eX.hom ≫ (b ≫ eY.inv) := Category.assoc _ _ _

private theorem cancel_fraction_target
    {C : Type v} [Category.{w} C] {P Q R S T : C}
    (d : P ⟶ Q) (a : Q ⟶ R) (e : S ≅ R) (r : T ⟶ P) (n : T ⟶ S)
    (h : r ≫ (d ≫ a ≫ e.inv) = n) : (r ≫ d) ≫ a = n ≫ e.hom := by
  have hc : (r ≫ (d ≫ a ≫ e.inv)) ≫ e.hom = (r ≫ d) ≫ a := by
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact hc.symm.trans (congrArg (fun q ↦ q ≫ e.hom) h)

variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable (F : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone F) (hs : IsLimit s)
variable [∀ {i j : Iᵒᵖ} (h : i ⟶ j), IsAffineHom (F.map h)]
variable [∀ i : Iᵒᵖ, CompactSpace (F.obj i)]
variable [∀ i : Iᵒᵖ, QuasiSeparatedSpace (F.obj i)]

include hs

/-- For two covers at the same stage, actual Hom descent supplies a right
fraction whose evaluation is the prescribed morphism at the limit. -/
theorem exists_stage_fraction
    (i : Iᵒᵖ) (A B : FiniteEtale (F.obj i))
    (a : (pullback (s.π.app i)).obj A ⟶ (pullback (s.π.app i)).obj B) :
    ∃ φ : (cartesian F).RightFraction
        ((stageInclusion F i).obj A) ((stageInclusion F i).obj B),
      (baseChange F s).map φ.s ≫ a = (baseChange F s).map φ.f := by
  obtain ⟨j, h, b, hb⟩ := exists_inverse_limit_stage_hom F s hs i A B a
  let dA := (transition F h).app A
  let dB := (transition F h).app B
  let n := (stageInclusion F j).map b ≫ dB
  let eA := (inverseLimitPullbackComparison F s h).app A
  let eB := (inverseLimitPullbackComparison F s h).app B
  let β := (pullback (s.π.app j)).map b
  have hdA : (baseChange F s).map dA = eA.inv :=
    baseChange_refinementHom F s ((stageInclusion F i).obj A) h
  have hdB : (baseChange F s).map dB = eB.inv :=
    baseChange_refinementHom F s ((stageInclusion F i).obj B) h
  have hβ : (baseChange F s).map ((stageInclusion F j).map b) = β :=
    (Functor.congr_hom (stageInclusion_comp_baseChange F s j) b).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hn : (baseChange F s).map n = β ≫ eB.inv :=
    ((baseChange F s).map_comp ((stageInclusion F j).map b) dB).trans
      (congrArg₂ (fun q r ↦ q ≫ r) hβ hdB)
  refine ⟨⟨dA, transition_cartesian F h A, n⟩, ?_⟩
  exact (congrArg (fun q ↦ q ≫ a) hdA).trans
    ((iso_square_inv eA eB a β hb).trans hn.symm)

/-- Common refinement reduces arbitrary model sources and targets to one
stage, where the actual finite-étale Hom-descent theorem applies. -/
theorem exists_fraction
    (A B : InverseLimitModel F)
    (a : (baseChange F s).obj A ⟶ (baseChange F s).obj B) :
    ∃ φ : (cartesian F).RightFraction A B,
      (baseChange F s).map φ.s ≫ a = (baseChange F s).map φ.f := by
  obtain ⟨k, hkA, hkB⟩ := exists_ge_ge A.right.unop B.right.unop
  let hA : op k ⟶ A.right := (homOfLE hkA).op
  let hB : op k ⟶ B.right := (homOfLE hkB).op
  let A' := refinementObj F A hA
  let B' := refinementObj F B hB
  let dA : A' ⟶ A := refinementHom F A hA
  let dB : B' ⟶ B := refinementHom F B hB
  let da : (baseChange F s).obj A' ⟶ (baseChange F s).obj A :=
    (baseChange F s).map dA
  let db : (baseChange F s).obj B' ⟶ (baseChange F s).obj B :=
    (baseChange F s).map dB
  have : IsIso db := baseChange_inverts_cartesian F s dB (refinementHom_cartesian F B hB)
  let eB : (baseChange F s).obj B' ≅ (baseChange F s).obj B := asIso db
  let a' : (baseChange F s).obj A' ⟶ (baseChange F s).obj B' := da ≫ a ≫ eB.inv
  obtain ⟨ψ, hψ⟩ := exists_stage_fraction F s hs (op k) (stageObj F A') (stageObj F B') a'
  let d := ψ.s ≫ dA
  let n := ψ.f ≫ dB
  have hd : cartesian F d :=
    (cartesian F).comp_mem ψ.s dA ψ.hs (refinementHom_cartesian F A hA)
  have hfactor : ((baseChange F s).map ψ.s ≫ da) ≫ a =
      (baseChange F s).map ψ.f ≫ db :=
    cancel_fraction_target da a eB ((baseChange F s).map ψ.s)
      ((baseChange F s).map ψ.f) hψ
  refine ⟨⟨d, hd, n⟩, ?_⟩
  exact (congrArg (fun q ↦ q ≫ a) ((baseChange F s).map_comp ψ.s dA)).trans
    (hfactor.trans ((baseChange F s).map_comp ψ.f dB).symm)

/-- The actual comparison out of the localization of finite-étale models
is full.  This is derived from native scheme Hom descent, not assumed. -/
theorem localizedBaseChange_full : (localizedBaseChange F s).Full := by
  constructor
  intro X Y a
  obtain ⟨A, rfl⟩ := (Localization.Construction.objEquiv (cartesian F)).surjective X
  obtain ⟨B, rfl⟩ := (Localization.Construction.objEquiv (cartesian F)).surjective Y
  obtain ⟨φ, hφ⟩ := exists_fraction F s hs A B a
  let Q := (cartesian F).Q
  let G := localizedBaseChange F s
  let f : Q.obj A ⟶ Q.obj B := φ.map Q (Localization.inverts Q (cartesian F))
  have : IsIso ((baseChange F s).map φ.s) := baseChange_inverts_cartesian F s φ.s φ.hs
  have hQs : G.map (Q.map φ.s) = (baseChange F s).map φ.s :=
    (Functor.congr_hom (q_comp_localizedBaseChange F s) φ.s).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hQf : G.map (Q.map φ.f) = (baseChange F s).map φ.f :=
    (Functor.congr_hom (q_comp_localizedBaseChange F s) φ.f).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hfactor : (baseChange F s).map φ.s ≫ G.map f = (baseChange F s).map φ.f := by
    have hcomp : G.map (Q.map φ.s) ≫ G.map f = G.map (Q.map φ.s ≫ f) :=
      (G.map_comp (Q.map φ.s) f).symm
    have hrel : Q.map φ.s ≫ f = Q.map φ.f :=
      φ.map_s_comp_map Q (Localization.inverts Q (cartesian F))
    exact (congrArg
      (fun q : (baseChange F s).obj φ.X' ⟶ (baseChange F s).obj A ↦ q ≫ G.map f)
      hQs.symm).trans
        (hcomp.trans ((congrArg (fun q : Q.obj φ.X' ⟶ Q.obj B ↦ G.map q) hrel).trans hQf))
  refine ⟨f, ?_⟩
  exact (cancel_epi ((baseChange F s).map φ.s)).1 (hfactor.trans hφ.symm)

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
