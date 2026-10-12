/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_LFP_exists_fg_nonempty_iso_pullbackAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Schemes.AffineLimit
import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.AlgebraicCurves.Geometry.Schemes.FGSubalgebraTensorStage
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_IsDirectLimit_exists_invertible_linearEquiv_baseChange
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_IsDirectLimit_exists_stage_linearEquiv_of_finitePresentation_compat
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Invertible_of_projective_of_forall_finrank_eq_one
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.SchemeTheory.CategoryTheory.ModuleCatTensorExtension

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.PicardGroup

/-!
# Descent of a rigidified line bundle to a finitely generated stage

For a curve with a two-affine-chart cover, this file descends a rigidified line bundle to a
finitely generated subalgebra of the coefficient algebra. The affine-chart modules and their
overlap maps are constructed at that stage, and the pulled-back underlying sheaf is isomorphic
to the original underlying sheaf.
-/

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

Private checking candidate for helpers intended to remain in the existing LFP source.
No existing implementation has been moved into this file.
-/

section CategoricalClutching

universe u v

open CategoryTheory TensorProduct

namespace ModuleCat

open scoped ChangeOfRings

/-- Tensor cancellation on a unit outer tensor is the coefficient map induced by g. -/
theorem cancelBaseChange_one_tmul_rTensor
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (g : S →ₐ[R] T) (M : ModuleCat.{u} R)
    (x : S ⊗[R] M) :
    let _ : Algebra S T := g.toRingHom.toAlgebra
    let _ : IsScalarTower R S T :=
      IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
    TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
        ((1 : T) ⊗ₜ[S] x) = g.toLinearMap.rTensor M x := by
  intro algebraST towerRST
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply]
    change (g s * 1) ⊗ₜ[R] m = g s ⊗ₜ[R] m
    rw [mul_one]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- A finite-presentation isomorphism descends as an isomorphism of scalar-extension
objects, with the canonical cocone comparison square proved in ModuleCat.
The stage owner's actual algebra hom is identified with the prescribed cocone map. -/
theorem exists_stage_iso_of_finitePresentation_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {K : Type u} [CommRing K]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra K (B i)]
    (τ : ∀ i j, i ≤ j → B i →ₐ[K] B j)
    [DirectedSystem B (fun i j h => τ i j h)]
    (U : Type u) [CommRing U] [Algebra K U]
    (g : ∀ i, B i →ₐ[K] U)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : U, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) (P Q : ModuleCat.{u} (B i₀))
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : (extendScalars (g i₀).toRingHom).obj P ≅
      (extendScalars (g i₀).toRingHom).obj Q) :
    ∃ (j : ι) (hj : i₀ ≤ j)
      (ej : (extendScalars (τ i₀ j hj).toRingHom).obj P ≅
        (extendScalars (τ i₀ j hj).toRingHom).obj Q),
      let hcomp : (g j).toRingHom.comp (τ i₀ j hj).toRingHom = (g i₀).toRingHom :=
        congrArg (fun f : B i₀ →ₐ[K] U => f.toRingHom) (hg i₀ j hj)
      let c : extendScalars (g i₀).toRingHom ≅
          extendScalars (τ i₀ j hj).toRingHom ⋙ extendScalars (g j).toRingHom :=
        (eqToIso (congrArg (fun f : B i₀ →+* U => extendScalars.{u, u, u} f) hcomp)).symm ≪≫
          extendScalarsComp (τ i₀ j hj).toRingHom (g j).toRingHom
      (extendScalars (g j).toRingHom).map ej.hom ≫ c.inv.app Q =
        c.inv.app P ≫ e.hom := by
  let : Algebra (B i₀) U := (g i₀).toRingHom.toAlgebra
  obtain ⟨j, hj, gj, hgj, ej, hcompat⟩ :=
    Module.IsDirectLimit.exists_stage_linearEquiv_of_finitePresentation_compat
      B τ U g hg hsurj hzero i₀ (fun _ => rfl) P Q e.toLinearEquiv
  let : Algebra (B i₀) (B j) := (τ i₀ j hj).toRingHom.toAlgebra
  let γ : B j →ₐ[B i₀] U :=
    { (g j).toRingHom with
      commutes' := fun b => DFunLike.congr_fun (hg i₀ j hj) b }
  have hgjEq : gj = γ := AlgHom.ext hgj
  rw [hgjEq] at hcompat
  let stageIso : (extendScalars (τ i₀ j hj).toRingHom).obj P ≅
      (extendScalars (τ i₀ j hj).toRingHom).obj Q := ej.toModuleIso
  refine ⟨j, hj, stageIso, ?_⟩
  let hcomp : (g j).toRingHom.comp (τ i₀ j hj).toRingHom = (g i₀).toRingHom :=
    congrArg (fun f : B i₀ →ₐ[K] U => f.toRingHom) (hg i₀ j hj)
  let c : extendScalars (g i₀).toRingHom ≅
      extendScalars (τ i₀ j hj).toRingHom ⋙ extendScalars (g j).toRingHom :=
    (eqToIso (congrArg (fun f : B i₀ →+* U => extendScalars.{u, u, u} f) hcomp)).symm ≪≫
      extendScalarsComp (τ i₀ j hj).toRingHom (g j).toRingHom
  change (extendScalars (g j).toRingHom).map stageIso.hom ≫ c.inv.app Q =
    c.inv.app P ≫ e.hom
  let : Algebra (B j) U := γ.toRingHom.toAlgebra
  let : IsScalarTower (B i₀) (B j) U :=
    IsScalarTower.of_algebraMap_eq fun b => (γ.commutes b).symm
  have hcp : c.app P =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₀) (B j) U U P).symm.toModuleIso :=
    extendScalars_comparison_eq_cancel (τ i₀ j hj).toRingHom (g j).toRingHom
      (g i₀).toRingHom hcomp P
  have hcq : c.app Q =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₀) (B j) U U Q).symm.toModuleIso :=
    extendScalars_comparison_eq_cancel (τ i₀ j hj).toRingHom (g j).toRingHom
      (g i₀).toRingHom hcomp Q
  apply ExtendScalars.hom_ext (f := (g j).toRingHom)
  intro x
  change (c.app Q).inv
      ((extendScalars (g j).toRingHom).map stageIso.hom ((1 : U) ⊗ₜ[B j,(g j).toRingHom] x)) =
    e.hom ((c.app P).inv ((1 : U) ⊗ₜ[B j,(g j).toRingHom] x))
  rw [ExtendScalars.map_tmul, hcq, hcp]
  change TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₀) (B j) U U Q
      ((1 : U) ⊗ₜ[B j] (ej x)) =
    e.hom (TensorProduct.AlgebraTensorModule.cancelBaseChange (B i₀) (B j) U U P
      ((1 : U) ⊗ₜ[B j] x))
  rw [cancelBaseChange_one_tmul_rTensor γ Q (ej x), cancelBaseChange_one_tmul_rTensor γ P x]
  exact (hcompat x).symm


/-- Raising both the chart stage and the overlap stage preserves the realization
 of a module. All four supplied squares are equalities of actual ring maps;
 the old realization square is derived from them. -/
theorem extendScalars_one_chart_pasting
    {B J C D V U : Type u}
    [CommRing B] [CommRing J] [CommRing C] [CommRing D] [CommRing V] [CommRing U]
    (a : B →+* J) (q : B →+* C) (r : J →+* D) (s : C →+* D)
    (p : B →+* V) (p' : J →+* V) (uC : C →+* U) (uD : D →+* U) (v : V →+* U)
    (hc : p'.comp a = p) (ho : uD.comp s = uC)
    (hd : r.comp a = s.comp q) (hn : uD.comp r = v.comp p')
    (X : ModuleCat.{u} B) (M : ModuleCat.{u} V)
    (e : (extendScalars p).obj X ≅ M) :
  let hu : uC.comp q = v.comp p := by
    calc
      uC.comp q = (uD.comp s).comp q :=
        congrArg (fun t : C →+* U => t.comp q) ho.symm
      _ = uD.comp (s.comp q) := rfl
      _ = uD.comp (r.comp a) := congrArg (fun t : B →+* D => uD.comp t) hd.symm
      _ = (uD.comp r).comp a := rfl
      _ = (v.comp p').comp a := congrArg (fun t : J →+* U => t.comp a) hn
      _ = v.comp p := congrArg (fun t : B →+* V => v.comp t) hc
  let L : ModuleCat.{u} J := (extendScalars a).obj X
  let Q : ModuleCat.{u} C := (extendScalars q).obj X
  let N : ModuleCat.{u} D := (extendScalars r).obj L
  let cChart : extendScalars p ≅ extendScalars a ⋙ extendScalars p' :=
    (eqToIso (congrArg (fun t : B →+* V => extendScalars.{u, u, u} t) hc)).symm ≪≫
      extendScalarsComp a p'
  let e' : (extendScalars p').obj L ≅ M := cChart.symm.app X ≪≫ e
  let cStage : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hd.symm)).symm ≪≫
      extendScalarsComp q s
  let stage : N ≅ (extendScalars s).obj Q :=
    (extendScalarsComp a r).symm.app X ≪≫ cStage.app X
  let cOld : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
    (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hu)).symm ≪≫
      extendScalarsComp q uC
  let oldRealization : (extendScalars uC).obj Q ≅ (extendScalars v).obj M :=
    cOld.symm.app X ≪≫ (extendScalarsComp p v).app X ≪≫ (extendScalars v).mapIso e
  let cNew : extendScalars (v.comp p') ≅ extendScalars r ⋙ extendScalars uD :=
    (eqToIso (congrArg (fun t : J →+* U => extendScalars.{u, u, u} t) hn)).symm ≪≫
      extendScalarsComp r uD
  let newRealization : (extendScalars uD).obj N ≅ (extendScalars v).obj M :=
    cNew.symm.app L ≪≫ (extendScalarsComp p' v).app L ≪≫ (extendScalars v).mapIso e'
  let cOverlap : extendScalars uC ≅ extendScalars s ⋙ extendScalars uD :=
    (eqToIso (congrArg (fun t : C →+* U => extendScalars.{u, u, u} t) ho)).symm ≪≫
      extendScalarsComp s uD
  (extendScalars uD).mapIso stage ≪≫ cOverlap.symm.app Q ≪≫ oldRealization =
    newRealization := by
  let hu : uC.comp q = v.comp p := by
    calc
      uC.comp q = (uD.comp s).comp q :=
        congrArg (fun t : C →+* U => t.comp q) ho.symm
      _ = uD.comp (s.comp q) := rfl
      _ = uD.comp (r.comp a) := congrArg (fun t : B →+* D => uD.comp t) hd.symm
      _ = (uD.comp r).comp a := rfl
      _ = (v.comp p').comp a := congrArg (fun t : J →+* U => t.comp a) hn
      _ = v.comp p := congrArg (fun t : B →+* V => v.comp t) hc
  let L : ModuleCat.{u} J := (extendScalars a).obj X
  let Q : ModuleCat.{u} C := (extendScalars q).obj X
  let N : ModuleCat.{u} D := (extendScalars r).obj L
  let cChart : extendScalars p ≅ extendScalars a ⋙ extendScalars p' :=
    (eqToIso (congrArg (fun t : B →+* V => extendScalars.{u, u, u} t) hc)).symm ≪≫
      extendScalarsComp a p'
  let e' : (extendScalars p').obj L ≅ M := cChart.symm.app X ≪≫ e
  let cStage : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hd.symm)).symm ≪≫
      extendScalarsComp q s
  let stage : N ≅ (extendScalars s).obj Q :=
    (extendScalarsComp a r).symm.app X ≪≫ cStage.app X
  let cOld : extendScalars (v.comp p) ≅ extendScalars q ⋙ extendScalars uC :=
    (eqToIso (congrArg (fun t : B →+* U => extendScalars.{u, u, u} t) hu)).symm ≪≫
      extendScalarsComp q uC
  let oldRealization : (extendScalars uC).obj Q ≅ (extendScalars v).obj M :=
    cOld.symm.app X ≪≫ (extendScalarsComp p v).app X ≪≫ (extendScalars v).mapIso e
  let cNew : extendScalars (v.comp p') ≅ extendScalars r ⋙ extendScalars uD :=
    (eqToIso (congrArg (fun t : J →+* U => extendScalars.{u, u, u} t) hn)).symm ≪≫
      extendScalarsComp r uD
  let newRealization : (extendScalars uD).obj N ≅ (extendScalars v).obj M :=
    cNew.symm.app L ≪≫ (extendScalarsComp p' v).app L ≪≫ (extendScalars v).mapIso e'
  let cOverlap : extendScalars uC ≅ extendScalars s ⋙ extendScalars uD :=
    (eqToIso (congrArg (fun t : C →+* U => extendScalars.{u, u, u} t) ho)).symm ≪≫
      extendScalarsComp s uD
  change (extendScalars uD).mapIso stage ≪≫ cOverlap.symm.app Q ≪≫ oldRealization =
    newRealization
  let k : (extendScalars (uD.comp (r.comp a))).obj X ≅ (extendScalars uD).obj N :=
    (extendScalarsComp (r.comp a) uD).app X ≪≫
      (extendScalars uD).mapIso ((extendScalarsComp a r).app X)
  let H : (extendScalars uD).obj N ⟶ (extendScalars v).obj M :=
    (extendScalars uD).map stage.hom ≫ cOverlap.inv.app Q ≫ oldRealization.hom
  apply CategoryTheory.Iso.ext
  change H = newRealization.hom
  apply (cancel_epi k.hom).mp
  apply ExtendScalars.hom_ext (f := uD.comp (r.comp a))
  intro x
  let xa : L := (extendRestrictScalarsAdj a).unit.app X x
  let xq : Q := (extendRestrictScalarsAdj q).unit.app X x
  let xr : N := (extendRestrictScalarsAdj r).unit.app L xa
  have hk : k.hom ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x) =
      (extendRestrictScalarsAdj uD).unit.app N xr := by
    change (extendScalars uD).map ((extendScalarsComp a r).hom.app X)
      ((extendScalarsComp (r.comp a) uD).hom.app X
        ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x)) = _
    have houter := extendScalars_comparison_hom_unit (r.comp a) uD
      (uD.comp (r.comp a)) rfl X x
    change (extendScalarsComp (r.comp a) uD).hom.app X
      ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x) = _ at houter
    rw [houter]
    have hinner := extendScalars_comparison_hom_unit a r (r.comp a) rfl X x
    change (extendScalarsComp a r).hom.app X
      ((extendRestrictScalarsAdj (r.comp a)).unit.app X x) = xr at hinner
    exact (extendScalars_map_unit uD ((extendScalarsComp a r).hom.app X)
      ((extendRestrictScalarsAdj (r.comp a)).unit.app X x)).trans
      (congrArg (fun z : N => (extendRestrictScalarsAdj uD).unit.app N z) hinner)
  have hstage : stage.hom xr = (extendRestrictScalarsAdj s).unit.app Q xq := by
    change cStage.hom.app X ((extendScalarsComp a r).inv.app X xr) = _
    have ha : (extendScalarsComp a r).inv.app X xr =
        (extendRestrictScalarsAdj (r.comp a)).unit.app X x :=
      extendScalars_comparison_inv_unit a r (r.comp a) rfl X x
    rw [ha]
    exact extendScalars_comparison_hom_unit q s (r.comp a) hd.symm X x
  have hold : oldRealization.hom ((extendRestrictScalarsAdj uC).unit.app Q xq) =
      (extendRestrictScalarsAdj v).unit.app M
        (e.hom ((extendRestrictScalarsAdj p).unit.app X x)) := by
    change (extendScalars v).map e.hom
      ((extendScalarsComp p v).hom.app X
        (cOld.inv.app X ((extendRestrictScalarsAdj uC).unit.app Q xq))) = _
    rw [extendScalars_comparison_inv_unit q uC (v.comp p) hu X x]
    have hp := extendScalars_comparison_hom_unit p v (v.comp p) rfl X x
    change (extendScalarsComp p v).hom.app X
      ((extendRestrictScalarsAdj (v.comp p)).unit.app X x) = _ at hp
    rw [hp]
    exact extendScalars_map_unit v e.hom ((extendRestrictScalarsAdj p).unit.app X x)
  have hnew : newRealization.hom ((extendRestrictScalarsAdj uD).unit.app N xr) =
      (extendRestrictScalarsAdj v).unit.app M
        (e.hom ((extendRestrictScalarsAdj p).unit.app X x)) := by
    change (extendScalars v).map e'.hom
      ((extendScalarsComp p' v).hom.app L
        (cNew.inv.app L ((extendRestrictScalarsAdj uD).unit.app N xr))) = _
    rw [extendScalars_comparison_inv_unit r uD (v.comp p') hn L xa]
    have hp := extendScalars_comparison_hom_unit p' v (v.comp p') rfl L xa
    change (extendScalarsComp p' v).hom.app L
      ((extendRestrictScalarsAdj (v.comp p')).unit.app L xa) = _ at hp
    rw [hp]
    exact (extendScalars_map_unit v e'.hom
      ((extendRestrictScalarsAdj p').unit.app L xa)).trans
      (congrArg
        (fun z : (extendScalars p).obj X =>
          (extendRestrictScalarsAdj v).unit.app M (e.hom z))
        (extendScalars_comparison_inv_unit a p' p hc X x))
  have hmiddle : cOverlap.inv.app Q
      ((extendScalars uD).map stage.hom ((extendRestrictScalarsAdj uD).unit.app N xr)) =
      (extendRestrictScalarsAdj uC).unit.app Q xq :=
    (congrArg
      (fun z : (extendScalars uD).obj ((extendScalars s).obj Q) => cOverlap.inv.app Q z)
      ((extendScalars_map_unit uD stage.hom xr).trans
        (congrArg
          (fun z : (extendScalars s).obj Q =>
            (extendRestrictScalarsAdj uD).unit.app ((extendScalars s).obj Q) z)
          hstage))).trans
      (extendScalars_comparison_inv_unit s uD uC ho Q xq)
  have hleft : H ((extendRestrictScalarsAdj uD).unit.app N xr) =
      newRealization.hom ((extendRestrictScalarsAdj uD).unit.app N xr) :=
    (congrArg
      (fun z : (extendScalars uC).obj Q => oldRealization.hom z) hmiddle).trans
      (hold.trans hnew.symm)
  clear_value H newRealization k
  have heval : H (k.hom ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x)) =
      newRealization.hom
        (k.hom ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x)) :=
    (congrArg (fun z : (extendScalars uD).obj N => H z) hk).trans
      (hleft.trans
        (congrArg (fun z : (extendScalars uD).obj N => newRealization.hom z) hk).symm)
  exact (ModuleCat.comp_apply k.hom H
    ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x)).trans
    (heval.trans (ModuleCat.comp_apply k.hom newRealization.hom
      ((extendRestrictScalarsAdj (uD.comp (r.comp a))).unit.app X x)).symm)


/-- Finite presentation is preserved by scalar extension along its prescribed ring map. -/
theorem finitePresentation_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Module.FinitePresentation S ((extendScalars f).obj M) := by
  let : Algebra R S := f.toAlgebra
  exact inferInstanceAs (Module.FinitePresentation S (S ⊗[R] M))

/-- The finite-stage isomorphism descent owner applies to a directed system of
 ring maps, using only the canonical lifted-integer scalar actions internally. -/
theorem exists_stage_iso_of_finitePresentation_ring_compat
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (τ : ∀ i j, i ≤ j → B i →+* B j)
    [DirectedSystem B (fun i j h => τ i j h)]
    (U : Type u) [CommRing U]
    (g : ∀ i, B i →+* U)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i)
    (hsurj : ∀ b : U, ∃ i x, g i x = b)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0)
    (i₀ : ι) (P Q : ModuleCat.{u} (B i₀))
    [Module.FinitePresentation (B i₀) P] [Module.FinitePresentation (B i₀) Q]
    (e : (extendScalars (g i₀)).obj P ≅ (extendScalars (g i₀)).obj Q) :
    ∃ (j : ι) (hj : i₀ ≤ j)
      (ej : (extendScalars (τ i₀ j hj)).obj P ≅ (extendScalars (τ i₀ j hj)).obj Q),
      let c : extendScalars (g i₀) ≅ extendScalars (τ i₀ j hj) ⋙ extendScalars (g j) :=
        (eqToIso (congrArg (fun f : B i₀ →+* U => extendScalars.{u, u, u} f)
          (hg i₀ j hj))).symm ≪≫ extendScalarsComp (τ i₀ j hj) (g j)
      (extendScalars (g j)).map ej.hom ≫ c.inv.app Q = c.inv.app P ≫ e.hom := by
  let : ∀ i, Algebra (ULift.{u} ℤ) (B i) := fun i => ULift.algebra' ℤ (B i)
  let : Algebra (ULift.{u} ℤ) U := ULift.algebra' ℤ U
  let τA : ∀ i j, i ≤ j → B i →ₐ[ULift.{u} ℤ] B j := fun i j hij =>
    { τ i j hij with
      commutes' := fun n => by
        change τ i j hij (n.down : B i) = (n.down : B j)
        exact map_intCast (τ i j hij) n.down }
  let gA : ∀ i, B i →ₐ[ULift.{u} ℤ] U := fun i =>
    { g i with
      commutes' := fun n => by
        change g i (n.down : B i) = (n.down : U)
        exact map_intCast (g i) n.down }
  have hgA : ∀ i j (h : i ≤ j), (gA j).comp (τA i j h) = gA i := by
    intro i j h
    exact AlgHom.ext fun b => RingHom.congr_fun (hg i j h) b
  exact exists_stage_iso_of_finitePresentation_compat B τA U gA hgA hsurj hzero i₀ P Q e

/-- A clutching isomorphism between realizations of two finitely presented stage
 modules descends after raising both chart stages to one common index. The module
 pair and its realization maps are canonical scalar extensions, and the complete
 clutching realization equality is proved. -/
theorem exists_common_stage_clutching
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (B0 B1 C : ι → Type u)
    [∀ i, CommRing (B0 i)] [∀ i, CommRing (B1 i)] [∀ i, CommRing (C i)]
    (τ0 : ∀ i j, i ≤ j → B0 i →+* B0 j)
    (τ1 : ∀ i j, i ≤ j → B1 i →+* B1 j)
    (τC : ∀ i j, i ≤ j → C i →+* C j)
    [DirectedSystem B0 (fun i j h => τ0 i j h)]
    [DirectedSystem B1 (fun i j h => τ1 i j h)]
    [DirectedSystem C (fun i j h => τC i j h)]
    (U0 U1 U : Type u) [CommRing U0] [CommRing U1] [CommRing U]
    (g0 : ∀ i, B0 i →+* U0) (g1 : ∀ i, B1 i →+* U1) (gC : ∀ i, C i →+* U)
    (hg0 : ∀ i j (h : i ≤ j), (g0 j).comp (τ0 i j h) = g0 i)
    (hg1 : ∀ i j (h : i ≤ j), (g1 j).comp (τ1 i j h) = g1 i)
    (hgC : ∀ i j (h : i ≤ j), (gC j).comp (τC i j h) = gC i)
    (hsurj : ∀ b : U, ∃ i x, gC i x = b)
    (hzero : ∀ i (x : C i), gC i x = 0 → ∃ (j : ι) (h : i ≤ j), τC i j h x = 0)
    (ρ0 : ∀ i, B0 i →+* C i) (ρ1 : ∀ i, B1 i →+* C i)
    (hρ0 : ∀ i j (h : i ≤ j), (τC i j h).comp (ρ0 i) = (ρ0 j).comp (τ0 i j h))
    (hρ1 : ∀ i j (h : i ≤ j), (τC i j h).comp (ρ1 i) = (ρ1 j).comp (τ1 i j h))
    (v0 : U0 →+* U) (v1 : U1 →+* U)
    (hlim0 : ∀ i, (gC i).comp (ρ0 i) = v0.comp (g0 i))
    (hlim1 : ∀ i, (gC i).comp (ρ1 i) = v1.comp (g1 i))
    (i0 i1 : ι) (P0 : ModuleCat.{u} (B0 i0)) (P1 : ModuleCat.{u} (B1 i1))
    [Module.FinitePresentation (B0 i0) P0] [Module.FinitePresentation (B1 i1) P1]
    (σlim : (extendScalars v0).obj ((extendScalars (g0 i0)).obj P0) ≅
      (extendScalars v1).obj ((extendScalars (g1 i1)).obj P1)) :
    ∃ (j : ι) (h0 : i0 ≤ j) (h1 : i1 ≤ j),
      let L0 : ModuleCat.{u} (B0 j) := (extendScalars (τ0 i0 j h0)).obj P0
      let L1 : ModuleCat.{u} (B1 j) := (extendScalars (τ1 i1 j h1)).obj P1
      let M0 : ModuleCat.{u} U0 := (extendScalars (g0 i0)).obj P0
      let M1 : ModuleCat.{u} U1 := (extendScalars (g1 i1)).obj P1
      let Q0 : ModuleCat.{u} (C j) := (extendScalars (ρ0 j)).obj L0
      let Q1 : ModuleCat.{u} (C j) := (extendScalars (ρ1 j)).obj L1
      ∃ (E0 : (extendScalars (g0 j)).obj L0 ≅ M0)
        (E1 : (extendScalars (g1 j)).obj L1 ≅ M1)
        (F0 : (extendScalars (gC j)).obj Q0 ≅ (extendScalars v0).obj M0)
        (F1 : (extendScalars (gC j)).obj Q1 ≅ (extendScalars v1).obj M1)
        (σj : Q0 ≅ Q1),
        (∀ x : L0,
          F0.hom ((extendRestrictScalarsAdj (gC j)).unit.app Q0
            (show Q0 from (extendRestrictScalarsAdj (ρ0 j)).unit.app L0 x)) =
          (extendRestrictScalarsAdj v0).unit.app M0
            (E0.hom ((extendRestrictScalarsAdj (g0 j)).unit.app L0 x))) ∧
        (∀ x : L1,
          F1.hom ((extendRestrictScalarsAdj (gC j)).unit.app Q1
            (show Q1 from (extendRestrictScalarsAdj (ρ1 j)).unit.app L1 x)) =
          (extendRestrictScalarsAdj v1).unit.app M1
            (E1.hom ((extendRestrictScalarsAdj (g1 j)).unit.app L1 x))) ∧
        (extendScalars (gC j)).mapIso σj ≪≫ F1 = F0 ≪≫ σlim := by
  obtain ⟨i2, h02, h12⟩ := directed_of (· ≤ ·) i0 i1
  let q0 : B0 i0 →+* C i2 := (ρ0 i2).comp (τ0 i0 i2 h02)
  let Q0 : ModuleCat.{u} (C i2) := (extendScalars q0).obj P0
  have : Module.FinitePresentation (C i2) Q0 := finitePresentation_extendScalars q0 P0
  have hu0 : (gC i2).comp q0 = v0.comp (g0 i0) := by
    calc
      (gC i2).comp q0 = ((gC i2).comp (ρ0 i2)).comp (τ0 i0 i2 h02) := rfl
      _ = (v0.comp (g0 i2)).comp (τ0 i0 i2 h02) :=
        congrArg (fun t : B0 i2 →+* U => t.comp (τ0 i0 i2 h02)) (hlim0 i2)
      _ = v0.comp (g0 i0) :=
        congrArg (fun t : B0 i0 →+* U0 => v0.comp t) (hg0 i0 i2 h02)
  let cOld0 : extendScalars (v0.comp (g0 i0)) ≅
      extendScalars q0 ⋙ extendScalars (gC i2) :=
    (eqToIso (congrArg (fun t : B0 i0 →+* U => extendScalars.{u, u, u} t) hu0)).symm ≪≫
      extendScalarsComp q0 (gC i2)
  let oldF0 : (extendScalars (gC i2)).obj Q0 ≅
      (extendScalars v0).obj ((extendScalars (g0 i0)).obj P0) :=
    cOld0.symm.app P0 ≪≫ (extendScalarsComp (g0 i0) v0).app P0 ≪≫
      (extendScalars v0).mapIso (Iso.refl ((extendScalars (g0 i0)).obj P0))
  let q1 : B1 i1 →+* C i2 := (ρ1 i2).comp (τ1 i1 i2 h12)
  let Q1 : ModuleCat.{u} (C i2) := (extendScalars q1).obj P1
  have : Module.FinitePresentation (C i2) Q1 := finitePresentation_extendScalars q1 P1
  have hu1 : (gC i2).comp q1 = v1.comp (g1 i1) := by
    calc
      (gC i2).comp q1 = ((gC i2).comp (ρ1 i2)).comp (τ1 i1 i2 h12) := rfl
      _ = (v1.comp (g1 i2)).comp (τ1 i1 i2 h12) :=
        congrArg (fun t : B1 i2 →+* U => t.comp (τ1 i1 i2 h12)) (hlim1 i2)
      _ = v1.comp (g1 i1) :=
        congrArg (fun t : B1 i1 →+* U1 => v1.comp t) (hg1 i1 i2 h12)
  let cOld1 : extendScalars (v1.comp (g1 i1)) ≅
      extendScalars q1 ⋙ extendScalars (gC i2) :=
    (eqToIso (congrArg (fun t : B1 i1 →+* U => extendScalars.{u, u, u} t) hu1)).symm ≪≫
      extendScalarsComp q1 (gC i2)
  let oldF1 : (extendScalars (gC i2)).obj Q1 ≅
      (extendScalars v1).obj ((extendScalars (g1 i1)).obj P1) :=
    cOld1.symm.app P1 ≪≫ (extendScalarsComp (g1 i1) v1).app P1 ≪≫
      (extendScalars v1).mapIso (Iso.refl ((extendScalars (g1 i1)).obj P1))
  let θ : (extendScalars (gC i2)).obj Q0 ≅ (extendScalars (gC i2)).obj Q1 :=
    oldF0 ≪≫ σlim ≪≫ oldF1.symm
  obtain ⟨j, h2j, β, hβ⟩ := exists_stage_iso_of_finitePresentation_ring_compat
    C τC U gC hgC hsurj hzero i2 Q0 Q1 θ
  have h0 : i0 ≤ j := le_trans h02 h2j
  have h1 : i1 ≤ j := le_trans h12 h2j
  let s : C i2 →+* C j := τC i2 j h2j
  let cOverlap : extendScalars (gC i2) ≅ extendScalars s ⋙ extendScalars (gC j) :=
    (eqToIso (congrArg (fun t : C i2 →+* U => extendScalars.{u, u, u} t)
      (hgC i2 j h2j))).symm ≪≫ extendScalarsComp s (gC j)
  change (extendScalars (gC j)).map β.hom ≫ cOverlap.inv.app Q1 =
    cOverlap.inv.app Q0 ≫ θ.hom at hβ
  let L0 : ModuleCat.{u} (B0 j) := (extendScalars (τ0 i0 j h0)).obj P0
  let M0 : ModuleCat.{u} U0 := (extendScalars (g0 i0)).obj P0
  let cChart0 : extendScalars (g0 i0) ≅
      extendScalars (τ0 i0 j h0) ⋙ extendScalars (g0 j) :=
    (eqToIso (congrArg (fun t : B0 i0 →+* U0 => extendScalars.{u, u, u} t)
      (hg0 i0 j h0))).symm ≪≫ extendScalarsComp (τ0 i0 j h0) (g0 j)
  let e0 : (extendScalars (g0 j)).obj L0 ≅ M0 :=
    cChart0.symm.app P0 ≪≫ Iso.refl M0
  let cNew0 : extendScalars (v0.comp (g0 j)) ≅
      extendScalars (ρ0 j) ⋙ extendScalars (gC j) :=
    (eqToIso (congrArg (fun t : B0 j →+* U => extendScalars.{u, u, u} t)
      (hlim0 j))).symm ≪≫ extendScalarsComp (ρ0 j) (gC j)
  let F0 : (extendScalars (gC j)).obj ((extendScalars (ρ0 j)).obj L0) ≅
      (extendScalars v0).obj M0 :=
    cNew0.symm.app L0 ≪≫ (extendScalarsComp (g0 j) v0).app L0 ≪≫
      (extendScalars v0).mapIso e0
  let L1 : ModuleCat.{u} (B1 j) := (extendScalars (τ1 i1 j h1)).obj P1
  let M1 : ModuleCat.{u} U1 := (extendScalars (g1 i1)).obj P1
  let cChart1 : extendScalars (g1 i1) ≅
      extendScalars (τ1 i1 j h1) ⋙ extendScalars (g1 j) :=
    (eqToIso (congrArg (fun t : B1 i1 →+* U1 => extendScalars.{u, u, u} t)
      (hg1 i1 j h1))).symm ≪≫ extendScalarsComp (τ1 i1 j h1) (g1 j)
  let e1 : (extendScalars (g1 j)).obj L1 ≅ M1 :=
    cChart1.symm.app P1 ≪≫ Iso.refl M1
  let cNew1 : extendScalars (v1.comp (g1 j)) ≅
      extendScalars (ρ1 j) ⋙ extendScalars (gC j) :=
    (eqToIso (congrArg (fun t : B1 j →+* U => extendScalars.{u, u, u} t)
      (hlim1 j))).symm ≪≫ extendScalarsComp (ρ1 j) (gC j)
  let F1 : (extendScalars (gC j)).obj ((extendScalars (ρ1 j)).obj L1) ≅
      (extendScalars v1).obj M1 :=
    cNew1.symm.app L1 ≪≫ (extendScalarsComp (g1 j) v1).app L1 ≪≫
      (extendScalars v1).mapIso e1
  have hd0 : (ρ0 j).comp (τ0 i0 j h0) = s.comp q0 := by
    have ht : (τ0 i2 j h2j).comp (τ0 i0 i2 h02) = τ0 i0 j h0 :=
      RingHom.ext fun x => DirectedSystem.map_map' τ0 h02 h2j x
    calc
      (ρ0 j).comp (τ0 i0 j h0) =
          (ρ0 j).comp ((τ0 i2 j h2j).comp (τ0 i0 i2 h02)) :=
        congrArg (fun t : B0 i0 →+* B0 j => (ρ0 j).comp t) ht.symm
      _ = ((ρ0 j).comp (τ0 i2 j h2j)).comp (τ0 i0 i2 h02) := rfl
      _ = ((τC i2 j h2j).comp (ρ0 i2)).comp (τ0 i0 i2 h02) :=
        congrArg (fun t : B0 i2 →+* C j => t.comp (τ0 i0 i2 h02))
          (hρ0 i2 j h2j).symm
      _ = s.comp q0 := rfl
  let cStage0 : extendScalars ((ρ0 j).comp (τ0 i0 j h0)) ≅
      extendScalars q0 ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B0 i0 →+* C j => extendScalars.{u, u, u} t) hd0.symm)).symm ≪≫
      extendScalarsComp q0 s
  let lam0 : (extendScalars (ρ0 j)).obj L0 ≅ (extendScalars s).obj Q0 :=
    (extendScalarsComp (τ0 i0 j h0) (ρ0 j)).symm.app P0 ≪≫ cStage0.app P0
  have hpaste0 := extendScalars_one_chart_pasting
    (τ0 i0 j h0) q0 (ρ0 j) s (g0 i0) (g0 j) (gC i2) (gC j) v0
    (hg0 i0 j h0) (hgC i2 j h2j) hd0 (hlim0 j)
    P0 M0 (Iso.refl M0)
  change (extendScalars (gC j)).mapIso lam0 ≪≫ cOverlap.symm.app Q0 ≪≫ oldF0 = F0
    at hpaste0
  have hd1 : (ρ1 j).comp (τ1 i1 j h1) = s.comp q1 := by
    have ht : (τ1 i2 j h2j).comp (τ1 i1 i2 h12) = τ1 i1 j h1 :=
      RingHom.ext fun x => DirectedSystem.map_map' τ1 h12 h2j x
    calc
      (ρ1 j).comp (τ1 i1 j h1) =
          (ρ1 j).comp ((τ1 i2 j h2j).comp (τ1 i1 i2 h12)) :=
        congrArg (fun t : B1 i1 →+* B1 j => (ρ1 j).comp t) ht.symm
      _ = ((ρ1 j).comp (τ1 i2 j h2j)).comp (τ1 i1 i2 h12) := rfl
      _ = ((τC i2 j h2j).comp (ρ1 i2)).comp (τ1 i1 i2 h12) :=
        congrArg (fun t : B1 i2 →+* C j => t.comp (τ1 i1 i2 h12))
          (hρ1 i2 j h2j).symm
      _ = s.comp q1 := rfl
  let cStage1 : extendScalars ((ρ1 j).comp (τ1 i1 j h1)) ≅
      extendScalars q1 ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B1 i1 →+* C j => extendScalars.{u, u, u} t) hd1.symm)).symm ≪≫
      extendScalarsComp q1 s
  let lam1 : (extendScalars (ρ1 j)).obj L1 ≅ (extendScalars s).obj Q1 :=
    (extendScalarsComp (τ1 i1 j h1) (ρ1 j)).symm.app P1 ≪≫ cStage1.app P1
  have hpaste1 := extendScalars_one_chart_pasting
    (τ1 i1 j h1) q1 (ρ1 j) s (g1 i1) (g1 j) (gC i2) (gC j) v1
    (hg1 i1 j h1) (hgC i2 j h2j) hd1 (hlim1 j)
    P1 M1 (Iso.refl M1)
  change (extendScalars (gC j)).mapIso lam1 ≪≫ cOverlap.symm.app Q1 ≪≫ oldF1 = F1
    at hpaste1
  let σj : (extendScalars (ρ0 j)).obj L0 ≅ (extendScalars (ρ1 j)).obj L1 :=
    lam0 ≪≫ β ≪≫ lam1.symm
  refine ⟨j, h0, h1, e0, e1, F0, F1, σj, ?_, ?_, ?_⟩
  · intro x
    exact extendScalars_realization_unit (ρ0 j) (g0 j) (gC j) v0 (hlim0 j) L0 M0 e0 x
  · intro x
    exact extendScalars_realization_unit (ρ1 j) (g1 j) (gC j) v1 (hlim1 j) L1 M1 e1 x
  · change (extendScalars (gC j)).mapIso σj ≪≫ F1 = F0 ≪≫ σlim
    have hβIso : (extendScalars (gC j)).mapIso β ≪≫ cOverlap.symm.app Q1 =
        cOverlap.symm.app Q0 ≪≫ θ := by
      apply CategoryTheory.Iso.ext
      exact hβ
    have hβRealized : (extendScalars (gC j)).mapIso β ≪≫ cOverlap.symm.app Q1 ≪≫ oldF1 =
        cOverlap.symm.app Q0 ≪≫ oldF0 ≪≫ σlim := by
      calc
        (extendScalars (gC j)).mapIso β ≪≫ cOverlap.symm.app Q1 ≪≫ oldF1 =
            ((extendScalars (gC j)).mapIso β ≪≫ cOverlap.symm.app Q1) ≪≫ oldF1 :=
          (Iso.trans_assoc _ _ _).symm
        _ = (cOverlap.symm.app Q0 ≪≫ θ) ≪≫ oldF1 :=
          congrArg (fun z => z ≪≫ oldF1) hβIso
        _ = cOverlap.symm.app Q0 ≪≫ oldF0 ≪≫ σlim := by
          simp only [θ, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
    clear_value F0 F1 oldF0 oldF1 lam0 lam1 cOverlap
    calc
      (extendScalars (gC j)).mapIso σj ≪≫ F1 =
          (extendScalars (gC j)).mapIso lam0 ≪≫ (extendScalars (gC j)).mapIso β ≪≫
            (extendScalars (gC j)).mapIso lam1.symm ≪≫ F1 := by
        simp only [σj, Functor.mapIso_trans, Iso.trans_assoc]
      _ = (extendScalars (gC j)).mapIso lam0 ≪≫ (extendScalars (gC j)).mapIso β ≪≫
          (extendScalars (gC j)).mapIso lam1.symm ≪≫
            (extendScalars (gC j)).mapIso lam1 ≪≫ cOverlap.symm.app Q1 ≪≫ oldF1 := by
        rw [← hpaste1]
      _ = (extendScalars (gC j)).mapIso lam0 ≪≫ (extendScalars (gC j)).mapIso β ≪≫
          cOverlap.symm.app Q1 ≪≫ oldF1 := by
        simp only [Functor.mapIso_symm, Iso.symm_self_id_assoc]
      _ = (extendScalars (gC j)).mapIso lam0 ≪≫ cOverlap.symm.app Q0 ≪≫ oldF0 ≪≫ σlim :=
        congrArg (fun z => (extendScalars (gC j)).mapIso lam0 ≪≫ z) hβRealized
      _ = ((extendScalars (gC j)).mapIso lam0 ≪≫ cOverlap.symm.app Q0 ≪≫ oldF0) ≪≫ σlim := by
        rw [Iso.trans_assoc, Iso.trans_assoc]
      _ = F0 ≪≫ σlim := congrArg (fun z => z ≪≫ σlim) hpaste0

/-- The canonical comparison for a commuting scalar-extension square transports
 a chart coefficient through the restriction ring map. -/
theorem extendScalars_square_unit_smul
    {B J C D : Type u} [CommRing B] [CommRing J] [CommRing C] [CommRing D]
    (a : B →+* J) (q : B →+* C) (r : J →+* D) (s : C →+* D)
    (hsquare : r.comp a = s.comp q) (X : ModuleCat.{u} B) (x : X) (j : J) :
    let c : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
      (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hsquare.symm)).symm ≪≫
        extendScalarsComp q s
    let κ : (extendScalars r).obj ((extendScalars a).obj X) ≅
        (extendScalars s).obj ((extendScalars q).obj X) :=
      (extendScalarsComp a r).symm.app X ≪≫ c.app X
    let xa : (extendScalars a).obj X := (extendRestrictScalarsAdj a).unit.app X x
    κ.hom ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) (j • xa)) =
      r j • (show (extendScalars s).obj ((extendScalars q).obj X) from
        (extendRestrictScalarsAdj s).unit.app ((extendScalars q).obj X)
          ((extendRestrictScalarsAdj q).unit.app X x)) := by
  let c : extendScalars (r.comp a) ≅ extendScalars q ⋙ extendScalars s :=
    (eqToIso (congrArg (fun t : B →+* D => extendScalars.{u, u, u} t) hsquare.symm)).symm ≪≫
      extendScalarsComp q s
  let κ : (extendScalars r).obj ((extendScalars a).obj X) ≅
      (extendScalars s).obj ((extendScalars q).obj X) :=
    (extendScalarsComp a r).symm.app X ≪≫ c.app X
  let xa : (extendScalars a).obj X := (extendRestrictScalarsAdj a).unit.app X x
  change κ.hom ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) (j • xa)) = _
  have hunit : κ.hom ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) xa) =
      (extendRestrictScalarsAdj s).unit.app ((extendScalars q).obj X)
        ((extendRestrictScalarsAdj q).unit.app X x) := by
    have hcontract := extendScalars_comparison_inv_unit a r (r.comp a) rfl X x
    change (extendScalarsComp a r).inv.app X
      ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) xa) = _ at hcontract
    exact (congrArg
      (fun z : (extendScalars (r.comp a)).obj X => c.hom.app X z) hcontract).trans
      (extendScalars_comparison_hom_unit q s (r.comp a) hsquare.symm X x)
  clear_value κ
  have hbalance : (extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) (j • xa) =
      r j • (show (extendScalars r).obj ((extendScalars a).obj X) from
        (extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) xa) :=
    ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X)).hom.map_smul j xa
  exact (congrArg
    (fun z : (extendScalars r).obj ((extendScalars a).obj X) => κ.hom z) hbalance).trans
    ((κ.hom.hom.map_smul (r j)
      ((extendRestrictScalarsAdj r).unit.app ((extendScalars a).obj X) xa)).trans
      (congrArg
        (fun z : (extendScalars s).obj ((extendScalars q).obj X) => r j • z) hunit))


universe w



universe w'

/-- Extend a chart realization through a supplied overlap realization.
The resulting equivalence satisfies the restriction law on the canonical
scalar-extension unit, using the original overlap law. -/
theorem exists_scalarExtension_realization
    {V U : Type u} [CommRing V] [CommRing U] (v : V →+* U)
    (M : ModuleCat.{u} V)
    {N : Type w} [AddCommGroup N] [Module V N]
    {O : Type w'} [AddCommGroup O] [Module U O]
    (I : M ≃ₗ[V] N)
    (J : let _ : Algebra V U := v.toAlgebra; U ⊗[V] N ≃ₗ[U] O)
    (r : N → O)
    (hJ : let _ : Algebra V U := v.toAlgebra;
      ∀ n : N, J ((1 : U) ⊗ₜ[V] n) = r n) :
    ∃ E : (extendScalars v).obj M ≃ₗ[U] O,
      ∀ m : M, E ((extendRestrictScalarsAdj v).unit.app M m) = r (I m) := by
  let : Algebra V U := v.toAlgebra
  let E : (extendScalars v).obj M ≃ₗ[U] O :=
    (LinearEquiv.baseChange V U M N I) ≪≫ₗ J
  refine ⟨E, ?_⟩
  intro m
  change J (LinearEquiv.baseChange V U M N I ((1 : U) ⊗ₜ[V] m)) = r (I m)
  rw [LinearEquiv.baseChange_tmul, hJ]

/-- Scalar extension along the specified ring map preserves invertibility.
The categorical object uses that same map's restricted scalar action, so the
existing tensor-base-change invertibility instance applies in a fixed context. -/
theorem invertible_extendScalars_of_invertible
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Module.Invertible S ((extendScalars f).obj M) := by
  let : Algebra R S := f.toAlgebra
  exact inferInstanceAs (Module.Invertible S (S ⊗[R] M))

/-- A commuting scalar-extension diagram remains compatible with its
specified realizations. The raw base-change map is interpreted with the same
fixed ring-map action as the categorical scalar-extension functor. -/
theorem realization_baseChange_compat
    {R U : Type u} [CommRing R] [CommRing U] (f : R →+* U)
    (X0 X1 : ModuleCat.{u} R) (Y0 Y1 : ModuleCat.{u} U)
    {N : Type w} [AddCommGroup N] [Module U N]
    (σ : X0 ≅ X1) (F0 : (extendScalars f).obj X0 ≅ Y0)
    (F1 : (extendScalars f).obj X1 ≅ Y1) (τ : Y0 ≅ Y1)
    (I0 : (extendScalars f).obj X0 ≃ₗ[U] N) (I1 : (extendScalars f).obj X1 ≃ₗ[U] N)
    (J0 : Y0 ≃ₗ[U] N) (J1 : Y1 ≃ₗ[U] N)
    (h0 : ∀ z : (extendScalars f).obj X0, I0 z = J0 (F0.hom z))
    (h1 : ∀ z : (extendScalars f).obj X1, I1 z = J1 (F1.hom z))
    (hτ : ∀ y : Y0, J1 (τ.hom y) = J0 y)
    (hsquare : (extendScalars f).mapIso σ ≪≫ F1 = F0 ≪≫ τ) :
    let _ : Algebra R U := f.toAlgebra
    ∀ z : U ⊗[R] X0,
      I1 (LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv z) = I0 z := by
  intro algebraRU z
  have hleft : ((extendScalars f).mapIso σ ≪≫ F1).hom z =
      F1.hom (LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv z) :=
    ModuleCat.comp_apply ((extendScalars f).mapIso σ).hom F1.hom z
  have heval : ((extendScalars f).mapIso σ ≪≫ F1).hom z = (F0 ≪≫ τ).hom z :=
    congrArg (fun e : (extendScalars f).obj X0 ≅ Y1 => e.hom z) hsquare
  have hright : (F0 ≪≫ τ).hom z = τ.hom (F0.hom z) :=
    ModuleCat.comp_apply F0.hom τ.hom z
  exact (h1 (LinearEquiv.baseChange R U X0 X1 σ.toLinearEquiv z)).trans
    ((congrArg J1 (hleft.symm.trans (heval.trans hright))).trans
      ((hτ (F0.hom z)).trans (h0 z).symm))

/-- Evaluate an overlap presentation on a chart generator, keeping both
coordinate modules in their native scalar-extension carriers. The three
primitive generator laws determine the realized value. -/
theorem presented_overlap_generator
    {J C D U : Type u} [CommRing J] [CommRing C] [CommRing D] [CommRing U]
    (r : J →+* D) (s : C →+* D) (t : C →+* U)
    (P : ModuleCat.{u} J) (Q : ModuleCat.{u} C)
    {X N : Type*} [AddCommGroup N] [Module U N]
    (g : J → X → P) (η : X → Q) (ψ : D → U) (b : X → N)
    (κ :
      let _ : Algebra J D := r.toAlgebra
      let _ : Algebra C D := s.toAlgebra
      D ⊗[J] P ≃ₗ[D] D ⊗[C] Q)
    (F :
      let _ : Algebra C D := s.toAlgebra
      let _ : Algebra C U := t.toAlgebra
      D ⊗[C] Q → U ⊗[C] Q)
    (I : (extendScalars t).obj Q ≃ₗ[U] N)
    (hκ :
      let _ : Algebra J D := r.toAlgebra
      let _ : Algebra C D := s.toAlgebra
      ∀ (j : J) (x : X), κ ((1 : D) ⊗ₜ[J] g j x) = r j ⊗ₜ[C] η x)
    (hF :
      let _ : Algebra C D := s.toAlgebra
      let _ : Algebra C U := t.toAlgebra
      ∀ (d : D) (q : Q), F (d ⊗ₜ[C] q) = ψ d ⊗ₜ[C] q)
    (hI : ∀ (a : U) (x : X), I (a ⊗ₜ[C,t] η x) = a • b x) :
    let _ : Algebra J D := r.toAlgebra
    let _ : Algebra C D := s.toAlgebra
    let _ : Algebra C U := t.toAlgebra
    ∀ (j : J) (x : X), I (F (κ ((1 : D) ⊗ₜ[J] g j x))) = ψ (r j) • b x := by
  intro algebraJD algebraCD algebraCU j x
  exact (congrArg (fun z : D ⊗[C] Q => I (F z)) (hκ j x)).trans
    ((congrArg I (hF (r j) (η x))).trans (hI (ψ (r j)) x))

end ModuleCat

namespace TensorProduct

/-- Extend the actual coefficient-linear coordinates of a module and compose
with its tensor presentation. The source scalar action is preserved through
its supplied tower, and the elementary-tensor law is constructed together. -/
theorem exists_presentation_of_linearCoordinates
    (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A]
    (S : Type*) [CommRing S] [Algebra k S]
    (B : Type*) [CommRing B] [Algebra B S]
    (L : Type*) [AddCommGroup L] [Module B L] [SMulCommClass B k S]
    {M : Type*} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[S] S ⊗[B] L) (F : A ⊗[k] (S ⊗[B] L) ≃ₗ[A] N) :
    ∃ E : A ⊗[k] M ≃ₗ[A] N,
      ∀ (a : A) (m : M), E (a ⊗ₜ[k] m) = F (a ⊗ₜ[k] e m) := by
  let E : A ⊗[k] M ≃ₗ[A] N :=
    (LinearEquiv.baseChange k A M (S ⊗[B] L) (e.restrictScalars k)) ≪≫ₗ F
  refine ⟨E, ?_⟩
  intro a m
  exact congrArg F
    (LinearEquiv.baseChange_tmul (R := k) (A := A) (M := M) (N := S ⊗[B] L)
      (e := e.restrictScalars k) a m)

/-- Extend coefficient-linear coordinates through a tensor presentation and
its A-linear realization, constructing the final equivalence and its complete
generator formula without rebuilding the coordinate restriction at the call site. -/
theorem exists_realized_presentation_of_linearCoordinates
    (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A]
    (S : Type*) [CommRing S] [Algebra k S]
    (B : Type*) [CommRing B] [Algebra B S]
    (L : Type*) [AddCommGroup L] [Module B L] [SMulCommClass B k S]
    {M : Type*} [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    {N : Type*} [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[S] S ⊗[B] L) (F : A ⊗[k] (S ⊗[B] L) ≃ₗ[A] Q)
    (G : Q ≃ₗ[A] N) :
    ∃ Z : A ⊗[k] M ≃ₗ[A] N,
      ∀ (a : A) (m : M), Z (a ⊗ₜ[k] m) = G (F (a ⊗ₜ[k] e m)) := by
  obtain ⟨E, hE⟩ := exists_presentation_of_linearCoordinates k A S B L e F
  let Z : A ⊗[k] M ≃ₗ[A] N := E ≪≫ₗ G
  exact ⟨Z, fun a m => congrArg G (hE a m)⟩

/-- Compose the supplied coordinate transition, tensor-presentation naturality,
and realization comparison on every elementary outer tensor. -/
theorem realized_presentation_coordinate_transition
    (k A S C : Type*) [CommRing k] [CommRing A] [CommRing S] [CommRing C]
    [Algebra k A] [Algebra k S] [Algebra C S] [SMulCommClass C k S]
    (Q0 Q1 : Type*) [AddCommGroup Q0] [Module C Q0] [AddCommGroup Q1] [Module C Q1]
    (σ : Q0 ≃ₗ[C] Q1)
    {Y0 Y1 X0 X1 N : Type*}
    (K0 : Y0 → S ⊗[C] Q0) (K1 : Y1 → S ⊗[C] Q1) (s : Y0 → Y1)
    (F0 : A ⊗[k] (S ⊗[C] Q0) → X0) (F1 : A ⊗[k] (S ⊗[C] Q1) → X1)
    (u : X0 → X1) (I0 : X0 → N) (I1 : X1 → N)
    (hK : ∀ y : Y0, K1 (s y) = LinearEquiv.baseChange C S Q0 Q1 σ (K0 y))
    (hF : ∀ (a : A) (z : S ⊗[C] Q0),
      F1 (a ⊗ₜ[k] LinearEquiv.baseChange C S Q0 Q1 σ z) = u (F0 (a ⊗ₜ[k] z)))
    (hI : ∀ x : X0, I1 (u x) = I0 x) :
    ∀ (a : A) (y : Y0),
      I1 (F1 (a ⊗ₜ[k] K1 (s y))) = I0 (F0 (a ⊗ₜ[k] K0 y)) := by
  intro a y
  exact (congrArg (fun z : S ⊗[C] Q1 => I1 (F1 (a ⊗ₜ[k] z))) (hK y)).trans
    ((congrArg I1 (hF a (K0 y))).trans (hI (F0 (a ⊗ₜ[k] K0 y))))

/-- Compose the coordinate, presentation and realization scalar laws at
the outer unit coefficient. No tensor action is reconstructed. -/
theorem scalar_compatibility_of_unit_presentation
    {A S U M P Q N : Type*} [Monoid A] [MulAction A U]
    [SMul S M] [SMul S P] [SMul U Q] [SMul U N]
    (φ : S → U) (e : M → P) (F : P → Q) (G : Q → N) (Z : M → N)
    (he : ∀ (s : S) (m : M), e (s • m) = s • e m)
    (hF : ∀ (s : S) (p : P), F (s • p) = ((1 : A) • φ s) • F p)
    (hG : ∀ (u : U) (q : Q), G (u • q) = u • G q)
    (hZ : ∀ m : M, Z m = G (F (e m))) :
    ∀ (s : S) (m : M), Z (s • m) = φ s • Z m := by
  intro s m
  exact (hZ (s • m)).trans
    ((congrArg (fun p : P => G (F p)) (he s m)).trans
      ((congrArg G (hF s (e m))).trans
        ((hG ((1 : A) • φ s) (F (e m))).trans
          ((congrArg (fun u : U => u • G (F (e m))) (one_smul A (φ s))).trans
            (congrArg (fun n : N => φ s • n) (hZ m).symm)))))

/-- A square of scalar-extended linear maps is determined by unit tensors
in additive coordinates. The coefficient tensors span the coordinate module,
and A-linearity then supplies every outer tensor coefficient. -/
theorem baseChange_square_of_coordinate_generators
    {k A B : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing B]
    {S L M N P Q : Type*}
    [AddCommGroup S] [Module B S] [AddCommGroup L] [Module B L]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (e : M ≃+ S ⊗[B] L) (r : M →ₗ[k] N) (r' : P →ₗ[A] Q)
    (Z : A ⊗[k] M ≃ₗ[A] P) (W : A ⊗[k] N ≃ₗ[A] Q)
    (hgen : ∀ (s : S) (l : L),
      W ((1 : A) ⊗ₜ[k] r (e.symm (s ⊗ₜ[B] l))) =
        r' (Z ((1 : A) ⊗ₜ[k] e.symm (s ⊗ₜ[B] l)))) :
    ∀ x : A ⊗[k] M, W (r.baseChange A x) = r' (Z x) := by
  have hunit : ∀ m : M, W ((1 : A) ⊗ₜ[k] r m) = r' (Z ((1 : A) ⊗ₜ[k] m)) := by
    intro m
    have hcoord : ∀ z : S ⊗[B] L,
        W ((1 : A) ⊗ₜ[k] r (e.symm z)) = r' (Z ((1 : A) ⊗ₜ[k] e.symm z)) := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul s l => exact hgen s l
      | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    simpa only [AddEquiv.symm_apply_apply] using hcoord (e m)
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a m =>
    rw [LinearMap.baseChange_tmul,
      show (a ⊗ₜ[k] r m : A ⊗[k] N) = a • ((1 : A) ⊗ₜ[k] r m) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      show (a ⊗ₜ[k] m : A ⊗[k] M) = a • ((1 : A) ⊗ₜ[k] m) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      map_smul W, map_smul Z, map_smul r', hunit]

/-- Transport a coordinate-generator square through supplied endpoint
presentations and a source coordinate law. The overlap coordinate carrier
requires no additional algebraic structure. -/
theorem baseChange_square_of_presented_coordinates
    {k A B : Type*} [CommRing k] [CommRing A] [Algebra k A] [baseRing : CommRing B]
    {S L M N P Q Y : Type*}
    [sourceAdd : AddCommGroup S] [sourceModule : Module B S] [AddCommGroup L] [Module B L]
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (e : M ≃+ S ⊗[B] L) (r : M →ₗ[k] N) (r' : P →ₗ[A] Q)
    (Z : A ⊗[k] M ≃ₗ[A] P) (W : A ⊗[k] N ≃ₗ[A] Q)
    (d : N → Y) (u : S ⊗[B] L → Y) (F : Y → Q) (G : S ⊗[B] L → P)
    (hW : ∀ n : N, W ((1 : A) ⊗ₜ[k] n) = F (d n))
    (hZ : ∀ m : M, Z ((1 : A) ⊗ₜ[k] m) = G (e m))
    (hd : ∀ m : M, d (r m) = u (e m))
    (hgen : ∀ (s : S) (l : L), F (u (s ⊗ₜ[B] l)) = r' (G (s ⊗ₜ[B] l))) :
    ∀ x : A ⊗[k] M, W (r.baseChange A x) = r' (Z x) := by
  apply baseChange_square_of_coordinate_generators e r r' Z W
  intro s l
  rw [hW, hd, hZ, AddEquiv.apply_symm_apply, hgen]

/-- Prove the base-change restriction square from the actual chart and overlap
coordinate presentations and their generated pure-tensor laws. -/
private theorem baseChange_square_of_native_chart_coordinates
    {k A B J C D U V : Type u}
    [CommRing k] [CommRing A] [CommRing B] [CommRing J]
    [CommRing C] [CommRing D] [CommRing U] [CommRing V]
    [Algebra k A]
    [algBJ : Algebra B J] [algBU : Algebra B U]
    [algJD : Algebra J D] [algCD : Algebra C D] [algCV : Algebra C V]
    [Algebra A U] [Algebra A V]
    {X Q : Type u} [AddCommGroup X] [Module B X]
    [AddCommGroup Q] [Module C Q]
    {M N T0 T1 : Type v}
    [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup T0] [Module A T0] [Module U T0]
    [AddCommGroup T1] [Module A T1] [Module V T1]
    (e : M ≃+ J ⊗[B] X)
    (sourceRestrict : M →ₗ[k] N) (targetRestrict : T0 →ₗ[A] T1)
    (Z : A ⊗[k] M ≃ₗ[A] T0) (W : A ⊗[k] N ≃ₗ[A] T1)
    (d : N → D ⊗[J] (J ⊗[B] X))
    (kappa : D ⊗[J] (J ⊗[B] X) ≃ₗ[D] D ⊗[C] Q)
    (newI : U ⊗[B] X ≃ₗ[U] T0) (Xi : V ⊗[C] Q ≃ₗ[V] T1)
    (G : J ⊗[B] X → U ⊗[B] X) (H : D ⊗[C] Q → V ⊗[C] Q)
    (eta : X → Q) (rho : J →+* D) (rhoU : U →+* V)
    (phi : J →+* U) (psi : D →+* V)
    (hKappa : ∀ (j : J) (x : X),
      kappa ((1 : D) ⊗ₜ[J] (j ⊗ₜ[B] x)) = rho j ⊗ₜ[C] eta x)
    (hPresent : ∀ (d : D) (q : Q),
      H (d ⊗ₜ[C] q) = ((1 : A) • psi d) ⊗ₜ[C] q)
    (hXi : ∀ (a : V) (x : X),
      Xi (a ⊗ₜ[C] eta x) = a • targetRestrict (newI ((1 : U) ⊗ₜ[B] x)))
    (hChart : ∀ (j : J) (x : X),
      G (j ⊗ₜ[B] x) = ((1 : A) • phi j) ⊗ₜ[B] x)
    (hW : ∀ n : N, W ((1 : A) ⊗ₜ[k] n) = Xi (H (kappa (d n))))
    (hZ : ∀ m : M, Z ((1 : A) ⊗ₜ[k] m) = newI (G (e m)))
    (hC : ∀ m : M, d (sourceRestrict m) = (1 : D) ⊗ₜ[J] e m)
    (hRestrict : ∀ (a : U) (m : T0),
      targetRestrict (a • m) = rhoU a • targetRestrict m)
    (hPhiRho : ∀ j : J, psi (rho j) = rhoU (phi j)) :
    ∀ x : A ⊗[k] M,
      W (sourceRestrict.baseChange A x) = targetRestrict (Z x) := by
  apply baseChange_square_of_presented_coordinates
    (B := B) (S := J) (L := X)
    (baseRing := inferInstanceAs (CommRing B))
    (sourceAdd := inferInstanceAs (AddCommGroup J))
    (sourceModule := inferInstanceAs (Module B J))
    e sourceRestrict targetRestrict Z W d
    (fun p : J ⊗[B] X => (1 : D) ⊗ₜ[J] p)
    (fun z : D ⊗[J] (J ⊗[B] X) => Xi (H (kappa z)))
    (fun p : J ⊗[B] X => newI (G p)) hW hZ hC
  intro j x
  let n : T0 := newI ((1 : U) ⊗ₜ[B] x)
  have hleft : Xi (H (kappa ((1 : D) ⊗ₜ[J] (j ⊗ₜ[B] x)))) =
      ((1 : A) • psi (rho j)) • targetRestrict n :=
    (congrArg (fun z : D ⊗[C] Q => Xi (H z)) (hKappa j x)).trans
      ((congrArg Xi (hPresent (rho j) (eta x))).trans
        (hXi ((1 : A) • psi (rho j)) x))
  have hright : targetRestrict (newI (G (j ⊗ₜ[B] x))) =
      rhoU ((1 : A) • phi j) • targetRestrict n := by
    have ht : (((1 : A) • phi j) ⊗ₜ[B] x : U ⊗[B] X) =
        ((1 : A) • phi j) • ((1 : U) ⊗ₜ[B] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact (congrArg (fun p : U ⊗[B] X => targetRestrict (newI p))
      (hChart j x)).trans
      ((congrArg targetRestrict ((congrArg newI ht).trans
        (LinearEquiv.map_smul newI ((1 : A) • phi j) ((1 : U) ⊗ₜ[B] x)))).trans
        (hRestrict ((1 : A) • phi j) n))
  have hc : (1 : A) • psi (rho j) = rhoU ((1 : A) • phi j) :=
    (one_smul A (psi (rho j))).trans
      ((hPhiRho j).trans (congrArg rhoU (one_smul A (phi j))).symm)
  exact hleft.trans ((congrArg (fun c : V => c • targetRestrict n) hc).trans hright.symm)

end TensorProduct

end CategoricalClutching

section ProofImplementation


namespace JacobianVarieties.Picard.Proofs.LFP_exists_fg_nonempty_iso_pullbackAlong
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u v w

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace LFP
open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

section ActR

variable (k : Type*) [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

/-- The action of a chart scalar on the module after base extension. -/
noncomputable def actR (s : Γ) : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P :=
  (DistribSMul.toLinearMap k P s).baseChange A'

@[scoped simp] theorem actR_tmul (s : Γ) (a : A') (m : P) :
    actR k A' s (a ⊗ₜ[k] m) = a ⊗ₜ[k] (s • m) := by
  simp only [actR, LinearMap.baseChange_tmul, DistribSMul.toLinearMap_apply]

theorem actR_one : actR k A' (1 : Γ) = (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  change actR k A' (1 : Γ) (a ⊗ₜ[k] m) = a ⊗ₜ[k] m
  rw [actR_tmul, one_smul]

theorem actR_mul (s t : Γ) : actR k A' (P := P) (s * t) = actR k A' s ∘ₗ actR k A' t := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  change actR k A' (s * t) (a ⊗ₜ[k] m) =
    actR k A' s (actR k A' t (a ⊗ₜ[k] m))
  simp only [actR_tmul, mul_smul]

theorem actR_add (s t : Γ) : actR k A' (P := P) (s + t) = actR k A' s + actR k A' t := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  change actR k A' (s + t) (a ⊗ₜ[k] m) =
    actR k A' s (a ⊗ₜ[k] m) + actR k A' t (a ⊗ₜ[k] m)
  simp only [actR_tmul, add_smul, tmul_add]

theorem rTensor_actR {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'') (s : Γ)
    (x : A' ⊗[k] P) :
    h.toLinearMap.rTensor P (actR k A' s x) = actR k A'' s (h.toLinearMap.rTensor P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [actR_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, actR_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_smul' {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (x : A' ⊗[k] Q) :
    h.toLinearMap.rTensor Q (a • x) = h a • h.toLinearMap.rTensor Q x := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem tmul_eq_smul_one_tmul {Q : Type*} [AddCommGroup Q] [Module k Q] (a : A') (m : Q) :
    a ⊗ₜ[k] m = a • ((1 : A') ⊗ₜ[k] m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end ActR

section Intertwines

variable {k : Type*} [CommRing k] {Γ Γ' Γ'' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ']
    [Algebra k Γ']
  [CommRing Γ''] [Algebra k Γ'']
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module Γ'' N] [Module k N] [IsScalarTower k Γ'' N]

/-- Compatibility of a linear map with the indicated actions of chart scalars. -/
def Intertwines (σ : Γ → Γ') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) : Prop :=
  ∀ (s : Γ) (x : A' ⊗[k] P), f (actR k A' s x) = actR k A' (σ s) (f x)

theorem Intertwines.comp {σ : Γ → Γ'} {σ' : Γ' → Γ''} {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    {g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N} (hf : Intertwines σ f) (hg : Intertwines σ' g) :
    Intertwines (σ' ∘ σ) (g ∘ₗ f) := fun s x => by
  change g (f (actR k A' s x)) = actR k A' (σ' (σ s)) (g (f x))
  rw [hf, hg]

theorem Intertwines.id : Intertwines (_root_.id : Γ → Γ) (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k]
    P) :=
  fun _ _ => rfl

theorem Intertwines.symm {e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q} {σ : Γ ≃ Γ'}
    (he : Intertwines σ (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    Intertwines σ.symm (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) := fun s y => by
  apply e.injective
  change e (e.symm (actR k A' s y)) = e (actR k A' (σ.symm s) (e.symm y))
  rw [LinearEquiv.apply_symm_apply]
  have := he (σ.symm s) (e.symm y)
  simp only [LinearEquiv.coe_coe, Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem Intertwines.baseChange (σ : Γ → Γ') (r : P →ₗ[k] Q) (hr : ∀ (s : Γ) (m : P), r (s • m) = σ
    s • r m) :
    Intertwines σ (r.baseChange A') := fun s x => by
  induction x using TensorProduct.inductionOn with
  | tmul a m => simp only [actR_tmul, LinearMap.baseChange_tmul, hr]
  | add x y hx hy => simp only [map_add, hx, hy]

end Intertwines

section Ext

variable {k : Type*} [CommRing k] {Γ : Type*} [CommRing Γ] [Algebra k Γ]
  {A' : Type*} [CommRing A'] [Algebra k A']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {N : Type*} [AddCommGroup N] [Module A' N]

theorem linearMap_ext_of_span (F G : A' ⊗[k] P →ₗ[A'] N) (T : Γ → N → N)
    (hF : ∀ (s : Γ) (x : A' ⊗[k] P), F (actR k A' s x) = T s (F x))
    (hG : ∀ (s : Γ) (x : A' ⊗[k] P), G (actR k A' s x) = T s (G x))
    (gens : Set P) (hgens : Submodule.span Γ gens = ⊤)
    (h : ∀ m ∈ gens, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)) : F = G := by
  let S : Submodule Γ P :=
    { carrier := {m | F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
      zero_mem' := by
        change F ((1 : A') ⊗ₜ[k] (0 : P)) = G ((1 : A') ⊗ₜ[k] (0 : P))
        simp only [tmul_zero, map_zero]
      smul_mem' := fun s m hm => by
        simp only [Set.mem_ofPred_eq] at hm ⊢
        rw [← actR_tmul k A', hF, hG, hm] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hgens, Submodule.span_le]; exact h
  have h1 : ∀ m : P, F ((1 : A') ⊗ₜ[k] m) = G ((1 : A') ⊗ₜ[k] m) := fun m => by
    have : m ∈ S := by rw [hS]; trivial
    exact this
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a m => rw [tmul_eq_smul_one_tmul k A', map_smul, map_smul, h1]
  | add x y hx hy => simp only [map_add, hx, hy]

end Ext

section Push

variable {k : Type*} [CommRing k] {Γ Γ' : Type*} [CommRing Γ] [Algebra k Γ] [CommRing Γ'] [Algebra
    k Γ']
  {A' A'' : Type*} [CommRing A'] [Algebra k A'] [CommRing A''] [Algebra k A'']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module k Q] [IsScalarTower k Γ' Q]
  {N : Type*} [AddCommGroup N] [Module k N]

private noncomputable def _root_.AlgebraicGeometry.RelPicard.LFP.push (h : A' →ₐ[k] A'') (f : A'
    ⊗[k] P →ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q :=
  LinearMap.liftBaseChange A''
    ((h.toLinearMap.rTensor Q) ∘ₗ (f.restrictScalars k) ∘ₗ (TensorProduct.mk k A' P 1))

open _root_.AlgebraicGeometry.RelPicard.LFP
@[scoped simp] theorem push_tmul (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (a : A'') (m
    : P) :
    push h f (a ⊗ₜ[k] m) = a • h.toLinearMap.rTensor Q (f ((1 : A') ⊗ₜ[k] m)) := by
  simp only [push, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply]

theorem push_rTensor (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (x : A' ⊗[k] P) :
    push h f (h.toLinearMap.rTensor P x) = h.toLinearMap.rTensor Q (f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, push_tmul, ← rTensor_smul' k A' h,
      ← map_smul, ← tmul_eq_smul_one_tmul k A']
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_id (h : A' →ₐ[k] A'') :
    push h (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) = LinearMap.id := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  change push h (LinearMap.id : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P) (a ⊗ₜ[k] m) =
    a ⊗ₜ[k] m
  rw [push_tmul, LinearMap.id_apply, LinearMap.rTensor_tmul,
    AlgHom.toLinearMap_apply, map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem push_comp (h : A' →ₐ[k] A'') (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)
    (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] N) :
    push h (g ∘ₗ f) = push h g ∘ₗ push h f := by
  ext m
  simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_restrictScalars, push_tmul, one_smul]
  rw [push_rTensor]

theorem Intertwines.push {σ : Γ → Γ'} (h : A' →ₐ[k] A'') {f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q}
    (hf : Intertwines σ f) : Intertwines σ (push h f) := fun s x => by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [actR_tmul, push_tmul, push_tmul, ← actR_tmul k A', hf, rTensor_actR, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem rTensor_baseChange (h : A' →ₐ[k] A'') {M M' : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M']
    [Module k M'] (r : M →ₗ[k] M') (x : A' ⊗[k] M) :
    h.toLinearMap.rTensor M' (r.baseChange A' x) = r.baseChange A'' (h.toLinearMap.rTensor M x) :=
        by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem push_square (h : A' →ₐ[k] A'') {P' : Type*} [AddCommGroup P'] [Module k P'] {Q' : Type*}
    [AddCommGroup Q']
    [Module k Q'] (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P') (g : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] Q')
    (r : P →ₗ[k] Q) (r' : P' →ₗ[k] Q') (hsq : ∀ x, g (r.baseChange A' x) = r'.baseChange A' (f x))
    (y : A'' ⊗[k] P) : push h g (r.baseChange A'' y) = r'.baseChange A'' (push h f y) := by
  induction y using TensorProduct.inductionOn with
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, push_tmul, push_tmul, map_smul, ← rTensor_baseChange, ← hsq,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_span_range_of_algEquiv {Γ'' : Type*} [CommRing Γ''] [Algebra A' Γ'']
    (e : A' ⊗[k] Γ ≃ₐ[A'] Γ'') (φ : Γ → Γ'') (he : ∀ s, e ((1 : A') ⊗ₜ[k] s) = φ s) (y : Γ'') :
    y ∈ Submodule.span A' (Set.range φ) := by
  obtain ⟨x, rfl⟩ := e.surjective y
  induction x using TensorProduct.inductionOn with
  | tmul a s =>
    rw [tmul_eq_smul_one_tmul k A' a s, map_smul, he]
    exact Submodule.smul_mem _ a (Submodule.subset_span ⟨s, rfl⟩)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- A tensor product equivalence extended along a homomorphism of base algebras. -/
noncomputable def pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    A'' ⊗[k] P ≃ₗ[A''] A'' ⊗[k] Q :=
  LinearEquiv.ofLinearMap (push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q))
    (push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P))
    (by rw [← push_comp, LinearEquiv.comp_symm, push_id])
    (by rw [← push_comp, LinearEquiv.symm_comp, push_id])

@[scoped simp] theorem pushEquiv_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) (x :
    A'' ⊗[k] P) :
    pushEquiv h e x = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) x := rfl

@[scoped simp] theorem pushEquiv_symm_apply (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (x : A'' ⊗[k] Q) :
    (pushEquiv h e).symm x = push h (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P) x := rfl

theorem coe_pushEquiv (h : A' →ₐ[k] A'') (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q) :
    (pushEquiv h e : A'' ⊗[k] P →ₗ[A''] A'' ⊗[k] Q) = push h (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) := rfl

end Push

section Orient

variable (k : Type*) [CommRing k] (Γ : Type*) [CommRing Γ] [Algebra k Γ]
  (A' : Type*) [CommRing A'] [Algebra k A']
  (P : Type*) [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]

/-- The equivalence reordering the tensor factors of a base extended module. -/
noncomputable def orient : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[k] A' ⊗[k] P :=
  ((TensorProduct.comm Γ (Γ ⊗[k] A') P).restrictScalars k) ≪≫ₗ
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k Γ Γ P A').restrictScalars k) ≪≫ₗ
  (TensorProduct.comm k P A')

@[scoped simp] theorem orient_tmul (γ : Γ) (a : A') (m : P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) ⊗ₜ[Γ] m) = a ⊗ₜ[k] (γ • m) := by
  change TensorProduct.comm k P A'
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k Γ Γ P A'
      (TensorProduct.comm Γ (Γ ⊗[k] A') P ((γ ⊗ₜ[k] a) ⊗ₜ[Γ] m))) =
    a ⊗ₜ[k] (γ • m)
  rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.comm_tmul]

@[scoped simp] theorem orient_symm_tmul (a : A') (m : P) :
    (orient k Γ A' P).symm (a ⊗ₜ[k] m) = ((1 : Γ) ⊗ₜ[k] a) ⊗ₜ[Γ] m := by
  rw [LinearEquiv.symm_apply_eq, orient_tmul, one_smul]

theorem orient_smul (γ : Γ) (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] a) • x) = a • actR k A' γ (orient k Γ A' P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    induction b using TensorProduct.inductionOn with
    | tmul γ' a' =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, orient_tmul,
        orient_tmul, actR_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_smul]
    | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem orient_smul_left (a : A') (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P (((1 : Γ) ⊗ₜ[k] a) • x) = a • orient k Γ A' P x := by
  rw [orient_smul, actR_one, LinearMap.id_apply]

theorem orient_smul_right (γ : Γ) (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A' P ((γ ⊗ₜ[k] (1 : A')) • x) = actR k A' γ (orient k Γ A' P x) := by
  rw [orient_smul, one_smul]

theorem orient_symm_smul (a : A') (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (a • y) = ((1 : Γ) ⊗ₜ[k] a) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_left, LinearEquiv.apply_symm_apply]

theorem orient_symm_actR (γ : Γ) (y : A' ⊗[k] P) :
    (orient k Γ A' P).symm (actR k A' γ y) = (γ ⊗ₜ[k] (1 : A')) • (orient k Γ A' P).symm y := by
  rw [LinearEquiv.symm_apply_eq, orient_smul_right, LinearEquiv.apply_symm_apply]

theorem orient_rTensor_map {A'' : Type*} [CommRing A''] [Algebra k A''] (h : A' →ₐ[k] A'')
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    orient k Γ A'' P ((Algebra.TensorProduct.map (AlgHom.id Γ Γ) h).toLinearMap.rTensor P x) =
      h.toLinearMap.rTensor P (orient k Γ A' P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b m =>
    induction b using TensorProduct.inductionOn with
    | tmul γ a =>
      simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, orient_tmul]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {k Γ A' P}
variable {Q : Type*} [AddCommGroup Q] [Module Γ Q] [Module k Q] [IsScalarTower k Γ Q]

/-- A linear map transported from the reordered tensor presentation. -/
noncomputable def fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q where
  toFun y := orient k Γ A' Q (f ((orient k Γ A' P).symm y))
  map_add' y y' := by simp only [map_add]
  map_smul' a y := by
    rw [orient_symm_smul, map_smul, orient_smul_left, RingHom.id_apply]

theorem fromOrient_apply (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A' ⊗[k] P) :
    fromOrient f y = orient k Γ A' Q (f ((orient k Γ A' P).symm y)) := rfl

theorem fromOrient_orient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    fromOrient f (orient k Γ A' P x) = orient k Γ A' Q (f x) := by
  rw [fromOrient_apply, LinearEquiv.symm_apply_apply]

theorem intertwines_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    Intertwines (_root_.id : Γ → Γ) (fromOrient f) := fun s y => by
  rw [fromOrient_apply, fromOrient_apply, orient_symm_actR, map_smul, orient_smul_right]; rfl

/-- A linear map compatible with chart scalars transported to the reordered tensor presentation. -/
noncomputable def toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ)
    f) :
    (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q where
  toFun x := (orient k Γ A' Q).symm (f (orient k Γ A' P x))
  map_add' x x' := by simp only [map_add]
  map_smul' b x := by
    rw [RingHom.id_apply]
    induction b using TensorProduct.inductionOn with
    | tmul γ a =>
      rw [orient_smul, map_smul, hf, LinearEquiv.symm_apply_eq, orient_smul,
          LinearEquiv.apply_symm_apply]
      rfl
    | add b b' hb hb' => simp only [add_smul, map_add, hb, hb']

theorem toOrient_apply (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ) f)
    (x : (Γ ⊗[k] A') ⊗[Γ] P) :
    toOrient f hf x = (orient k Γ A' Q).symm (f (orient k Γ A' P x)) := rfl

theorem fromOrient_toOrient (f : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) (hf : Intertwines (_root_.id : Γ → Γ)
    f) :
    fromOrient (toOrient f hf) = f := by
  refine LinearMap.ext fun y => ?_
  rw [fromOrient_apply, toOrient_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem toOrient_fromOrient (f : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    toOrient (fromOrient f) (intertwines_fromOrient f) = f := by
  refine LinearMap.ext fun x => ?_
  rw [toOrient_apply, fromOrient_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- An equivalence transported from the reordered tensor presentation. -/
noncomputable def fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) :
    A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q :=
  LinearEquiv.ofLinearMap (fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q))
    (fromOrient (e.symm : (Γ ⊗[k] A') ⊗[Γ] Q →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] P))
    (by
      refine LinearMap.ext fun y => ?_
      change orient k Γ A' Q
        (e ((orient k Γ A' P).symm
          (orient k Γ A' P (e.symm ((orient k Γ A' Q).symm y))))) = y
      rw [(orient k Γ A' P).symm_apply_apply, e.apply_symm_apply,
        (orient k Γ A' Q).apply_symm_apply])
    (by
      refine LinearMap.ext fun y => ?_
      change orient k Γ A' P
        (e.symm ((orient k Γ A' Q).symm
          (orient k Γ A' Q (e ((orient k Γ A' P).symm y))))) = y
      rw [(orient k Γ A' Q).symm_apply_apply, e.symm_apply_apply,
        (orient k Γ A' P).apply_symm_apply])

@[scoped simp] theorem coe_fromOrientEquiv (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ]
    Q) :
    (fromOrientEquiv e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) =
      fromOrient (e : (Γ ⊗[k] A') ⊗[Γ] P →ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) := rfl

theorem fromOrientEquiv_apply (e : (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q) (y : A'
    ⊗[k] P) :
    fromOrientEquiv e y = orient k Γ A' Q (e ((orient k Γ A' P).symm y)) := rfl

/-- An equivalence compatible with chart scalars transported to the reordered tensor presentation.
-/
noncomputable def toOrientEquiv (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) :
    (Γ ⊗[k] A') ⊗[Γ] P ≃ₗ[Γ ⊗[k] A'] (Γ ⊗[k] A') ⊗[Γ] Q :=
  LinearEquiv.ofLinearMap (toOrient (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q) he)
    (toOrient (e.symm : A' ⊗[k] Q →ₗ[A'] A' ⊗[k] P)
      (Intertwines.symm (σ := Equiv.refl Γ) he))
    (by
      refine LinearMap.ext fun y => ?_
      change (orient k Γ A' Q).symm
        (e (orient k Γ A' P
          ((orient k Γ A' P).symm (e.symm (orient k Γ A' Q y))))) = y
      rw [(orient k Γ A' P).apply_symm_apply, e.apply_symm_apply,
        (orient k Γ A' Q).symm_apply_apply])
    (by
      refine LinearMap.ext fun y => ?_
      change (orient k Γ A' P).symm
        (e.symm (orient k Γ A' Q
          ((orient k Γ A' Q).symm (e (orient k Γ A' P y))))) = y
      rw [(orient k Γ A' Q).apply_symm_apply, e.symm_apply_apply,
        (orient k Γ A' P).symm_apply_apply])

theorem toOrientEquiv_apply (e : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] Q)
    (he : Intertwines (_root_.id : Γ → Γ) (e : A' ⊗[k] P →ₗ[A'] A' ⊗[k] Q)) (x : (Γ ⊗[k] A') ⊗[Γ]
        P) :
    toOrientEquiv e he x = (orient k Γ A' Q).symm (e (orient k Γ A' P x)) := rfl

end Orient

section OneChart

variable {k : Type*} [CommRing k] {A' : Type*} [CommRing A'] [Algebra k A']
  {Γ : Type*} [CommRing Γ] [Algebra k Γ] {Γ' : Type*} [CommRing Γ'] [Algebra A' Γ']
  {P : Type*} [AddCommGroup P] [Module Γ P] [Module k P] [IsScalarTower k Γ P]
  {P' : Type*} [AddCommGroup P'] [Module Γ P'] [Module k P'] [IsScalarTower k Γ P']
  {Q : Type*} [AddCommGroup Q] [Module Γ' Q] [Module A' Q] [IsScalarTower A' Γ' Q]
  {Q' : Type*} [AddCommGroup Q'] [Module Γ' Q'] [Module A' Q'] [IsScalarTower A' Γ' Q']

omit [Algebra k A'] in
theorem smul_comm_of_tower (a : A') (t : Γ') (q : Q) : a • t • q = t • a • q := by
  rw [← algebraMap_smul Γ' a (t • q), smul_smul, mul_comm, ← smul_smul, algebraMap_smul]

theorem apply_actR_of_semilinear (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q)
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (s : Γ) (x : A' ⊗[k] P) : β (actR k A' s x) = φ s • β x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    rw [actR_tmul, tmul_eq_smul_one_tmul k A' a (s • m), map_smul, hs, tmul_eq_smul_one_tmul k A'
        a m,
      map_smul, smul_comm_of_tower]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem symm_apply_smul_of_semilinear (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q)
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (s : Γ) (q : Q) : β.symm (φ s • q) = actR k A' s (β.symm q) := by
  rw [LinearEquiv.symm_apply_eq, apply_actR_of_semilinear φ β hs, LinearEquiv.apply_symm_apply]

/-- The equivalence between tensor presentations induced by the two chart comparison equivalences.
-/
noncomputable def conjIn (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q') (ψ : Q ≃ₗ[Γ'] Q') :
    A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P' :=
  β ≪≫ₗ ψ.restrictScalars A' ≪≫ₗ β'.symm

theorem conjIn_apply (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q') (ψ : Q ≃ₗ[Γ'] Q')
    (x : A' ⊗[k] P) : conjIn β β' ψ x = β'.symm (ψ (β x)) := rfl

theorem intertwines_conjIn (φ : Γ → Γ') (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (ψ : Q ≃ₗ[Γ'] Q') :
    Intertwines (_root_.id : Γ → Γ) (conjIn β β' ψ : A' ⊗[k] P →ₗ[A'] A' ⊗[k] P') := fun s x => by
  simp only [LinearEquiv.coe_coe, conjIn_apply]
  rw [apply_actR_of_semilinear φ β hs, map_smul, symm_apply_smul_of_semilinear φ β' hs']; rfl

/-- The chart scalar linear equivalence induced from a compatible equivalence of tensor
    presentations. -/
noncomputable def conjOut (φ : Γ → Γ') (hgen : ∀ y : Γ', y ∈ Submodule.span A' (Set.range φ))
    (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (f : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P') (hf : Intertwines (_root_.id : Γ → Γ) (f : A' ⊗[k] P →ₗ[A']
        A' ⊗[k] P')) :
    Q ≃ₗ[Γ'] Q' :=
  let E : Q ≃ₗ[A'] Q' := β.symm ≪≫ₗ f ≪≫ₗ β'
  have hE : ∀ (y : Γ') (q : Q), E (y • q) = y • E q := fun y q => by
    suffices h : Submodule.span A' (Set.range φ) ≤
        { carrier := {y : Γ' | ∀ q : Q, E (y • q) = y • E q}
          add_mem' := fun {a b} ha hb q => by
            simp only [Set.mem_ofPred_eq] at ha hb ⊢; rw [add_smul, map_add, ha, hb, add_smul]
          zero_mem' := fun q => by simp only [zero_smul, map_zero]
          smul_mem' := fun a y hy q => by
            simp only [Set.mem_ofPred_eq] at hy ⊢
            rw [smul_assoc, map_smul, hy, smul_assoc] } from h (hgen y) q
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩ q
    simp only [E, LinearEquiv.trans_apply]
    rw [symm_apply_smul_of_semilinear φ β hs, ← LinearEquiv.coe_coe f, hf, LinearEquiv.coe_coe,
      apply_actR_of_semilinear φ β' hs']
    rfl
  { toFun := E
    invFun := E.symm
    map_add' := fun x y => E.map_add x y
    map_smul' := hE
    left_inv := E.left_inv
    right_inv := E.right_inv }

theorem conjOut_apply (φ : Γ → Γ') (hgen : ∀ y : Γ', y ∈ Submodule.span A' (Set.range φ))
    (β : A' ⊗[k] P ≃ₗ[A'] Q) (β' : A' ⊗[k] P' ≃ₗ[A'] Q')
    (hs : ∀ (s : Γ) (m : P), β ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β ((1 : A') ⊗ₜ[k] m))
    (hs' : ∀ (s : Γ) (m : P'), β' ((1 : A') ⊗ₜ[k] (s • m)) = φ s • β' ((1 : A') ⊗ₜ[k] m))
    (f : A' ⊗[k] P ≃ₗ[A'] A' ⊗[k] P') (hf : Intertwines (_root_.id : Γ → Γ) (f : A' ⊗[k] P →ₗ[A']
        A' ⊗[k] P'))
    (q : Q) : conjOut φ hgen β β' hs hs' f hf q = β' (f (β.symm q)) := rfl

end OneChart

section TwoChart

open TwoChartCech

variable {k : Type u} [CommRing k] {A' : Type u} [CommRing A'] [Algebra k A']
  {𝒰 : Cover.{u, u} k} {𝒰' : Cover.{u, u} A'}

/-- Chart section comparisons for base extension, compatible with restrictions and chart scalars. -/
structure ChartBC (φ0 : 𝒰.A0 → 𝒰'.A0) (φ1 : 𝒰.A1 → 𝒰'.A1) (φ01 : 𝒰.A01 → 𝒰'.A01)
    (S : Sections.{u, u, w} 𝒰) (T : Sections.{u, u, w} 𝒰') where
  /-- The first chart section equivalence after extending the base ring. -/
  β0 : A' ⊗[k] S.M0 ≃ₗ[A'] T.M0
  /-- The second chart section equivalence after extending the base ring. -/
  β1 : A' ⊗[k] S.M1 ≃ₗ[A'] T.M1
  /-- The overlap section equivalence after extending the base ring. -/
  β01 : A' ⊗[k] S.M01 ≃ₗ[A'] T.M01
  /-- Compatibility with restriction from the first chart to the overlap. -/
  hr0 : ∀ x, β01 (S.r0.baseChange A' x) = T.r0 (β0 x)
  /-- Compatibility with restriction from the second chart to the overlap. -/
  hr1 : ∀ x, β01 (S.r1.baseChange A' x) = T.r1 (β1 x)
  /-- Compatibility with the first chart scalar action on pure tensor generators. -/
  hs0 : ∀ (s : 𝒰.A0) (m : S.M0), β0 ((1 : A') ⊗ₜ[k] (s • m)) = φ0 s • β0 ((1 : A') ⊗ₜ[k] m)
  /-- Compatibility with the second chart scalar action on pure tensor generators. -/
  hs1 : ∀ (s : 𝒰.A1) (m : S.M1), β1 ((1 : A') ⊗ₜ[k] (s • m)) = φ1 s • β1 ((1 : A') ⊗ₜ[k] m)
  /-- Compatibility with the overlap scalar action on pure tensor generators. -/
  hs01 : ∀ (s : 𝒰.A01) (m : S.M01), β01 ((1 : A') ⊗ₜ[k] (s • m)) = φ01 s • β01 ((1 : A') ⊗ₜ[k] m)

variable {φ0 : 𝒰.A0 → 𝒰'.A0} {φ1 : 𝒰.A1 → 𝒰'.A1} {φ01 : 𝒰.A01 → 𝒰'.A01}
  {S S' : Sections.{u, u, w} 𝒰} {T T' : Sections.{u, u, w} 𝒰'}

theorem ChartBC.exists_intertwines_of_chartIso (β : ChartBC φ0 φ1 φ01 S T) (β' : ChartBC φ0 φ1 φ01
    S' T')
    (ψ0 : T.M0 ≃ₗ[𝒰'.A0] T'.M0) (ψ1 : T.M1 ≃ₗ[𝒰'.A1] T'.M1) (ψ01 : T.M01 ≃ₗ[𝒰'.A01] T'.M01)
    (hψ0 : ∀ m, ψ01 (T.r0 m) = T'.r0 (ψ0 m)) (hψ1 : ∀ m, ψ01 (T.r1 m) = T'.r1 (ψ1 m)) :
    ∃ (e0 : A' ⊗[k] S.M0 ≃ₗ[A'] A' ⊗[k] S'.M0) (e1 : A' ⊗[k] S.M1 ≃ₗ[A'] A' ⊗[k] S'.M1)
      (e01 : A' ⊗[k] S.M01 ≃ₗ[A'] A' ⊗[k] S'.M01),
      Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (e0 : A' ⊗[k] S.M0 →ₗ[A'] A' ⊗[k] S'.M0) ∧
      Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (e1 : A' ⊗[k] S.M1 →ₗ[A'] A' ⊗[k] S'.M1) ∧
      Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (e01 : A' ⊗[k] S.M01 →ₗ[A'] A' ⊗[k] S'.M01) ∧
      (∀ x, e01 (S.r0.baseChange A' x) = S'.r0.baseChange A' (e0 x)) ∧
      (∀ x, e01 (S.r1.baseChange A' x) = S'.r1.baseChange A' (e1 x)) := by
  refine ⟨conjIn β.β0 β'.β0 ψ0, conjIn β.β1 β'.β1 ψ1, conjIn β.β01 β'.β01 ψ01,
    intertwines_conjIn φ0 _ _ β.hs0 β'.hs0 ψ0, intertwines_conjIn φ1 _ _ β.hs1 β'.hs1 ψ1,
    intertwines_conjIn φ01 _ _ β.hs01 β'.hs01 ψ01, fun x => ?_, fun x => ?_⟩
  · rw [conjIn_apply, conjIn_apply, LinearEquiv.symm_apply_eq]
    change ψ01 (β.β01 _) = β'.β01 (S'.r0.baseChange A' (β'.β0.symm (ψ0 (β.β0 x))))
    rw [β.hr0, β'.hr0, LinearEquiv.apply_symm_apply, hψ0]
  · rw [conjIn_apply, conjIn_apply, LinearEquiv.symm_apply_eq]
    change ψ01 (β.β01 _) = β'.β01 (S'.r1.baseChange A' (β'.β1.symm (ψ1 (β.β1 x))))
    rw [β.hr1, β'.hr1, LinearEquiv.apply_symm_apply, hψ1]

theorem ChartBC.exists_chartIso_of_intertwines (β : ChartBC φ0 φ1 φ01 S T) (β' : ChartBC φ0 φ1 φ01
    S' T')
    (hgen0 : ∀ y : 𝒰'.A0, y ∈ Submodule.span A' (Set.range φ0))
    (hgen1 : ∀ y : 𝒰'.A1, y ∈ Submodule.span A' (Set.range φ1))
    (hgen01 : ∀ y : 𝒰'.A01, y ∈ Submodule.span A' (Set.range φ01))
    (f0 : A' ⊗[k] S.M0 ≃ₗ[A'] A' ⊗[k] S'.M0) (f1 : A' ⊗[k] S.M1 ≃ₗ[A'] A' ⊗[k] S'.M1)
    (f01 : A' ⊗[k] S.M01 ≃ₗ[A'] A' ⊗[k] S'.M01)
    (hf0 : Intertwines (_root_.id : 𝒰.A0 → 𝒰.A0) (f0 : A' ⊗[k] S.M0 →ₗ[A'] A' ⊗[k] S'.M0))
    (hf1 : Intertwines (_root_.id : 𝒰.A1 → 𝒰.A1) (f1 : A' ⊗[k] S.M1 →ₗ[A'] A' ⊗[k] S'.M1))
    (hf01 : Intertwines (_root_.id : 𝒰.A01 → 𝒰.A01) (f01 : A' ⊗[k] S.M01 →ₗ[A'] A' ⊗[k] S'.M01))
    (hsq0 : ∀ x, f01 (S.r0.baseChange A' x) = S'.r0.baseChange A' (f0 x))
    (hsq1 : ∀ x, f01 (S.r1.baseChange A' x) = S'.r1.baseChange A' (f1 x)) :
    ∃ (E0 : T.M0 ≃ₗ[𝒰'.A0] T'.M0) (E1 : T.M1 ≃ₗ[𝒰'.A1] T'.M1) (E01 : T.M01 ≃ₗ[𝒰'.A01] T'.M01),
      (∀ m, E01 (T.r0 m) = T'.r0 (E0 m)) ∧ (∀ m, E01 (T.r1 m) = T'.r1 (E1 m)) := by
  refine ⟨conjOut φ0 hgen0 β.β0 β'.β0 β.hs0 β'.hs0 f0 hf0, conjOut φ1 hgen1 β.β1 β'.β1 β.hs1
      β'.hs1 f1 hf1,
    conjOut φ01 hgen01 β.β01 β'.β01 β.hs01 β'.hs01 f01 hf01, fun m => ?_, fun m => ?_⟩
  · rw [conjOut_apply, conjOut_apply]
    obtain ⟨x, rfl⟩ := β.β0.surjective m
    rw [← β.hr0, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hsq0, β'.hr0]
  · rw [conjOut_apply, conjOut_apply]
    obtain ⟨x, rfl⟩ := β.β1.surjective m
    rw [← β.hr1, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hsq1, β'.hr1]

end TwoChart

section Present

variable (k : Type*) [CommRing k] (A' : Type*) [CommRing A'] [Algebra k A']
  (S : Type*) [CommRing S] [Algebra k S] (S' : Type*) [CommRing S'] [Algebra k S'] [Algebra A' S']
  [IsScalarTower k A' S']
  (B : Type*) [CommRing B] [Algebra B S] [Algebra B S']
  (L : Type*) [AddCommGroup L] [Module B L]
  [SMulCommClass B k S] [SMulCommClass B A' S']


theorem exists_presentEquiv (φ : S →+* S') (e : A' ⊗[k] S ≃ₐ[A'] S') (he : ∀ s, e ((1 : A') ⊗ₜ[k]
    s) = φ s)
    (hB : ∀ b, algebraMap B S' b = φ (algebraMap B S b)) :
    ∃ Z : A' ⊗[k] (S ⊗[B] L) ≃ₗ[A'] S' ⊗[B] L,
      (∀ (a : A') (s : S) (l : L), Z (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l) ∧
      (∀ (a : A') (s : S) (p : S ⊗[B] L), Z (a ⊗ₜ[k] (s • p)) = (a • φ s) • Z ((1 : A') ⊗ₜ[k] p))
          := by
  let : Algebra S S' := φ.toAlgebra
  have : IsScalarTower B S S' := IsScalarTower.of_algebraMap_eq fun b => by
    rw [RingHom.algebraMap_toAlgebra]; exact hB b
  let ce : S ⊗[k] A' ≃ₐ[k] S' := (Algebra.TensorProduct.comm k S A').trans (e.restrictScalars k)
  have hce : ∀ (s : S) (a : A'), ce (s ⊗ₜ[k] a) = φ s * algebraMap A' S' a := fun s a => by
    change e (a ⊗ₜ[k] s) = _
    rw [show a ⊗ₜ[k] s = (a ⊗ₜ[k] (1 : S)) * ((1 : A') ⊗ₜ[k] s) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, he,
      show a ⊗ₜ[k] (1 : S) = algebraMap A' (A' ⊗[k] S) a from rfl, AlgEquiv.commutes, mul_comm]
  let e' : S ⊗[k] A' ≃ₗ[S] S' :=
    { toFun := ce, invFun := ce.symm, map_add' := fun x y => map_add ce x y
      map_smul' := fun s x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_self,
          RingHom.id_apply, map_mul, hce, map_one, mul_one, Algebra.smul_def,
              RingHom.algebraMap_toAlgebra]
      left_inv := ce.left_inv, right_inv := ce.right_inv }
  have he' : ∀ a : A', e' ((1 : S) ⊗ₜ[k] a) = algebraMap A' S' a := fun a => by
    change ce _ = _; rw [hce, map_one, one_mul]
  let Zf : A' ⊗[k] (S ⊗[B] L) → S' ⊗[B] L := fun x =>
    TensorProduct.AlgebraTensorModule.cancelBaseChange B S S' S' L
      (LinearEquiv.rTensor (S ⊗[B] L) e' ((orient k S A' (S ⊗[B] L)).symm x))
  let Zg : S' ⊗[B] L → A' ⊗[k] (S ⊗[B] L) := fun y =>
    orient k S A' (S ⊗[B] L) ((LinearEquiv.rTensor (S ⊗[B] L) e').symm
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange B S S' S' L).symm y))
  have hadd : ∀ x y, Zf (x + y) = Zf x + Zf y := fun x y => by simp only [Zf, map_add]
  have hZ : ∀ (a : A') (s : S) (l : L),
      Zf (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l := fun a s l => by
    simp only [Zf]
    rw [orient_symm_tmul, LinearEquiv.rTensor_tmul, he',
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.smul_def, RingHom.algebraMap_toAlgebra, Algebra.smul_def, mul_comm]
  have hZs : ∀ (a : A') (s : S) (p : S ⊗[B] L), Zf (a ⊗ₜ[k] (s • p)) = (a • φ s) • Zf ((1 : A')
      ⊗ₜ[k] p) := by
    intro a s p
    induction p using TensorProduct.inductionOn with
    | tmul u l =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, hZ, hZ, one_smul, TensorProduct.smul_tmul',
          smul_eq_mul, map_mul,
        smul_mul_assoc]
    | add x y hx hy => simp only [smul_add, tmul_add, hadd, hx, hy]
  have hlin : ∀ (a : A') (x : A' ⊗[k] (S ⊗[B] L)), Zf (a • x) = a • Zf x := by
    intro a x
    induction x using TensorProduct.inductionOn with
    | tmul a' p =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      induction p using TensorProduct.inductionOn with
      | tmul s l => rw [hZ, hZ, TensorProduct.smul_tmul', mul_smul]
      | add x y hx hy => simp only [tmul_add, hadd, smul_add, hx, hy]
    | add x y hx hy => simp only [smul_add, hadd, hx, hy]
  have hgf : ∀ x, Zg (Zf x) = x := fun x => by simp only [Zf, Zg, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  have hfg : ∀ y, Zf (Zg y) = y := fun y => by simp only [Zf, Zg, LinearEquiv.symm_apply_apply,
      LinearEquiv.apply_symm_apply]
  let Z : A' ⊗[k] (S ⊗[B] L) ≃ₗ[A'] S' ⊗[B] L :=
    { toFun := Zf
      invFun := Zg
      map_add' := hadd
      map_smul' := hlin
      left_inv := hgf
      right_inv := hfg }
  exact ⟨Z, hZ, hZs⟩

end Present

/-- A tensor presentation commutes with a map of its coefficient module.
The evaluation map on the left coefficient need not itself be linear. -/
theorem tensorPresentation_naturality
    {B S U L M : Type*} [CommRing B]
    [AddCommGroup S] [Module B S] [AddCommGroup U] [Module B U]
    [AddCommGroup L] [Module B L] [AddCommGroup M] [Module B M]
    (χ : S → U)
    (F : S ⊗[B] L →+ U ⊗[B] L) (G : S ⊗[B] M →+ U ⊗[B] M)
    (hF : ∀ s l, F (s ⊗ₜ[B] l) = χ s ⊗ₜ[B] l)
    (hG : ∀ s m, G (s ⊗ₜ[B] m) = χ s ⊗ₜ[B] m)
    (f : L →ₗ[B] M) (x : S ⊗[B] L) :
    G (TensorProduct.map (LinearMap.id : S →ₗ[B] S) f x) =
      TensorProduct.map (LinearMap.id : U →ₗ[B] U) f (F x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s l =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, hG, hF,
      TensorProduct.map_tmul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor presentations commute with the actual scalar-extension maps of
an equivalence of coefficient modules. Only their pure-tensor presentation
laws are required; no module comparison is assumed. -/
theorem tensorPresentation_baseChange_naturality
    (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A]
    (S : Type*) [CommRing S] [Algebra k S]
    (U : Type*) [CommRing U] [Algebra A U]
    (B : Type*) [CommRing B] [Algebra B S] [Algebra B U]
    (L : Type*) [AddCommGroup L] [Module B L]
    (M : Type*) [AddCommGroup M] [Module B M]
    [SMulCommClass B k S] [SMulCommClass B A U]
    (φ : S → U)
    (F : A ⊗[k] (S ⊗[B] L) ≃ₗ[A] U ⊗[B] L)
    (G : A ⊗[k] (S ⊗[B] M) ≃ₗ[A] U ⊗[B] M)
    (hF : ∀ (a : A) (s : S) (l : L),
      F (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l)
    (hG : ∀ (a : A) (s : S) (m : M),
      G (a ⊗ₜ[k] (s ⊗ₜ[B] m)) = (a • φ s) ⊗ₜ[B] m)
    (e : L ≃ₗ[B] M) (a : A) (z : S ⊗[B] L) :
    G (a ⊗ₜ[k] LinearEquiv.baseChange B S L M e z) =
      LinearEquiv.baseChange B U L M e (F (a ⊗ₜ[k] z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul s l =>
    rw [LinearEquiv.baseChange_tmul, hG, hF, LinearEquiv.baseChange_tmul]
  | add x y hx hy => simp only [map_add, tmul_add, hx, hy]

/-- Construct both coefficient-module presentations over one ring
presentation, together with their scalar law and the actual base-change
naturality law for the supplied coefficient equivalence. -/
theorem exists_presentEquivs_natural
    (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A]
    (S : Type*) [CommRing S] [Algebra k S]
    (U : Type*) [CommRing U] [Algebra k U] [Algebra A U] [IsScalarTower k A U]
    (B : Type*) [CommRing B] [Algebra B S] [Algebra B U]
    (L : Type*) [AddCommGroup L] [Module B L]
    (M : Type*) [AddCommGroup M] [Module B M]
    [SMulCommClass B k S] [SMulCommClass B A U]
    (φ : S →+* U) (e : A ⊗[k] S ≃ₐ[A] U)
    (he : ∀ s, e ((1 : A) ⊗ₜ[k] s) = φ s)
    (hB : ∀ b, algebraMap B U b = φ (algebraMap B S b))
    (σ : L ≃ₗ[B] M) :
    ∃ (F : A ⊗[k] (S ⊗[B] L) ≃ₗ[A] U ⊗[B] L)
      (G : A ⊗[k] (S ⊗[B] M) ≃ₗ[A] U ⊗[B] M),
      (∀ (a : A) (s : S) (l : L),
        F (a ⊗ₜ[k] (s ⊗ₜ[B] l)) = (a • φ s) ⊗ₜ[B] l) ∧
      (∀ (a : A) (s : S) (p : S ⊗[B] L),
        F (a ⊗ₜ[k] (s • p)) = (a • φ s) • F ((1 : A) ⊗ₜ[k] p)) ∧
      (∀ (a : A) (s : S) (m : M),
        G (a ⊗ₜ[k] (s ⊗ₜ[B] m)) = (a • φ s) ⊗ₜ[B] m) ∧
      ∀ (a : A) (z : S ⊗[B] L),
        G (a ⊗ₜ[k] LinearEquiv.baseChange B S L M σ z) =
          LinearEquiv.baseChange B U L M σ (F (a ⊗ₜ[k] z)) := by
  obtain ⟨F, hF, hFs⟩ := exists_presentEquiv k A S U B L φ e he hB
  obtain ⟨G, hG, _⟩ := exists_presentEquiv k A S U B M φ e he hB
  refine ⟨F, G, hF, hFs, hG, ?_⟩
  intro a z
  exact tensorPresentation_baseChange_naturality k A S U B L M φ F G hF hG σ a z


end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace LFP
open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

section Vertex

variable {ι : Type v} {B₀ : Type u} [CommRing B₀] {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i,
    Algebra B₀ (B i)]
    {Bω : Type u} [CommRing Bω] [Algebra B₀ Bω] {Bω' : Type u} [CommRing Bω'] [Algebra B₀ Bω']

theorem vertex_comp [Preorder ι] (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) (g : ∀ i, B i →ₐ[B₀] Bω)
    (hg : ∀ i j (h : i ≤ j), (g j).comp (τ i j h) = g i) (h : Bω ≃ₐ[B₀] Bω') (i j : ι) (hij : i ≤
        j) :
    ((h : Bω →ₐ[B₀] Bω').comp (g j)).comp (τ i j hij) = (h : Bω →ₐ[B₀] Bω').comp (g i) := by
  rw [AlgHom.comp_assoc, hg]

theorem vertex_surj (g : ∀ i, B i →ₐ[B₀] Bω) (hsurj : ∀ b : Bω, ∃ i x, g i x = b) (h : Bω ≃ₐ[B₀]
    Bω')
    (b : Bω') : ∃ i x, ((h : Bω →ₐ[B₀] Bω').comp (g i)) x = b := by
  obtain ⟨i, x, hx⟩ := hsurj (h.symm b)
  refine ⟨i, x, ?_⟩
  change h (g i x) = b
  rw [hx, h.apply_symm_apply]

theorem vertex_zero [Preorder ι] (τ : ∀ i j, i ≤ j → B i →ₐ[B₀] B j) (g : ∀ i, B i →ₐ[B₀] Bω)
    (hzero : ∀ i (x : B i), g i x = 0 → ∃ (j : ι) (h : i ≤ j), τ i j h x = 0) (h : Bω ≃ₐ[B₀] Bω')
    (i : ι) (x : B i) (hx : ((h : Bω →ₐ[B₀] Bω').comp (g i)) x = 0) : ∃ (j : ι) (hij : i ≤ j), τ i
        j hij x = 0 :=
  hzero i x (h.injective (hx.trans (map_zero h).symm))

end Vertex

theorem smulCommClass_of_algebras (R₁ R₂ T : Type*) [CommSemiring R₁] [CommSemiring R₂]
    [CommSemiring T]
    [Algebra R₁ T] [Algebra R₂ T] : SMulCommClass R₁ R₂ T :=
  ⟨fun a b t => by simp only [Algebra.smul_def]; ring⟩

theorem one_tmul_tmul_tmul {B0 B' B'' V : Type*} [CommRing B0] [CommRing B'] [CommRing B'']
    [CommRing V]
    [Algebra B0 B'] [Algebra B' B''] [Algebra B'' V] {L : Type*} [AddCommGroup L] [Module B0 L]
    (b : B'') (β : B') (l : L) :
    ((1 : V) ⊗ₜ[B''] (b ⊗ₜ[B'] (β ⊗ₜ[B0] l)) : V ⊗[B''] (B'' ⊗[B'] (B' ⊗[B0] L))) =
      (algebraMap B'' V (β • b)) ⊗ₜ[B''] ((1 : B'') ⊗ₜ[B'] ((1 : B') ⊗ₜ[B0] l)) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one,
    TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finrank_baseChange_eq_one_of_invertible {A : Type*} [CommRing A] (P : Type*) [AddCommGroup
    P] [Module A P]
    [Module.Invertible A P] (K : Type*) [Field K] [Algebra A K] : Module.finrank K (K ⊗[A] P) = 1 :=
  Module.Invertible.finrank_eq_one K (K ⊗[A] P)

end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry

open CategoryTheory Opposite

namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Hom
open _root_.AlgebraicGeometry.Scheme.Hom
end Scheme.Hom
open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom in
theorem Scheme.Hom.appLE_app_apply_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X
    ⟶ Z)
    (h : f ≫ g = k) (U : Z.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (s : Γ(Z, U)) : (f.appLE (g ⁻¹ᵁ U) V e).hom ((g.app U).hom s) =
      (k.appLE U V (by
        subst h
        exact e)).hom s := by
  subst h
  rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom in
theorem Scheme.Hom.appLE_apply_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') (hU : U' ≤ U) (hV : V' ≤ V) (s : Γ(Y, U)) :
    (f.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom s) =
      (X.presheaf.map (homOfLE hV).op).hom ((f.appLE U V e).hom s) := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

open scoped _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom in
theorem Scheme.Hom.app_apply_map {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U) (s
    : Γ(Y, U)) :
    (f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom s) =
      (X.presheaf.map (homOfLE (show f ⁻¹ᵁ U' ≤ f ⁻¹ᵁ U from fun _ hx => hU hx)).op).hom ((f.app
          U).hom s) := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace LFP
open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

section VertexGeo

open _root_.AlgebraicGeometry.FGSubalgebra

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (Γ : Type u) [CommRing Γ] [Algebra R Γ]

/-- The chart algebra structure transported through the tensor presentation. -/
@[reducible] noncomputable def algebraOfPresent (U : Type u) [CommRing U] [Algebra A U] (eU : A
    ⊗[R] Γ ≃ₐ[A] U) :
    Algebra Γ U :=
  ((eU : A ⊗[R] Γ ≃+* U).toRingHom.comp (Algebra.TensorProduct.includeRight : Γ →ₐ[R] A ⊗[R]
      Γ).toRingHom).toAlgebra

/-- The reversed tensor presentation of the chart algebra. -/
noncomputable def vtxEquiv (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    Γ ⊗[R] A ≃ₐ[Γ] U := by
  intro chartAlgebra
  exact AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm R Γ A).toRingEquiv.trans (eU : A ⊗[R] Γ ≃+* U))
    (fun _ => rfl)

/-- The chart algebra homomorphism from a finitely generated tensor stage to the limit. -/
noncomputable def vtxHom (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U) (D :
    FGSubalgebra R A) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    tensorStage R A Γ D →ₐ[Γ] U := by
  intro chartAlgebra
  exact (vtxEquiv R A Γ U eU : Γ ⊗[R] A →ₐ[Γ] U).comp (tensorStageToColimit R A Γ D)

variable (U : Type u) [CommRing U] [Algebra A U] (eU : A ⊗[R] Γ ≃ₐ[A] U)

theorem vtxHom_tmul (D : FGSubalgebra R A) (γ : Γ) (d : ↥D.1) :
    vtxHom R A Γ U eU D (γ ⊗ₜ[R] d) = eU ((d : A) ⊗ₜ[R] γ) := rfl

theorem vtxHom_comp (i j : FGSubalgebra R A) (h : i ≤ j) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    (vtxHom R A Γ U eU j).comp (tensorStageMap R A Γ i j h) = vtxHom R A Γ U eU i := by
  intro chartAlgebra
  exact vertex_comp (fun i j h => tensorStageMap R A Γ i j h) (tensorStageToColimit R A Γ)
    (tensorStageToColimit_comp R A Γ) (vtxEquiv R A Γ U eU) i j h

theorem vtxHom_surj (b : U) : ∃ (i : FGSubalgebra R A) (x : tensorStage R A Γ i), vtxHom R A Γ U
    eU i x = b :=
  let := algebraOfPresent R A Γ U eU
  vertex_surj (tensorStageToColimit R A Γ) (tensorStageToColimit_surj R A Γ) (vtxEquiv R A Γ U eU) b

theorem vtxHom_zero (i : FGSubalgebra R A) (x : tensorStage R A Γ i) (hx : vtxHom R A Γ U eU i x =
    0) :
    ∃ (j : FGSubalgebra R A) (h : i ≤ j), tensorStageMap R A Γ i j h x = 0 :=
  let := algebraOfPresent R A Γ U eU
  vertex_zero (fun i j h => tensorStageMap R A Γ i j h) (tensorStageToColimit R A Γ)
      (tensorStageToColimit_zero R A Γ)
    (vtxEquiv R A Γ U eU) i x hx

/-- The ring homomorphism from a tensor stage to its chart presentation. -/
noncomputable def stgHom (D : FGSubalgebra R A) (W : Type u) [CommRing W] [Algebra (↥D.1) W]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) : tensorStage R A Γ D →+* W :=
  (eW : ↥D.1 ⊗[R] Γ ≃+* W).toRingHom.comp (Algebra.TensorProduct.comm R Γ ↥D.1 : Γ ⊗[R] ↥D.1 ≃ₐ[R]
      ↥D.1 ⊗[R] Γ).toRingHom

theorem stgHom_tmul (D : FGSubalgebra R A) (W : Type u) [CommRing W] [Algebra (↥D.1) W]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) (γ : Γ) (d : ↥D.1) : stgHom R A Γ D W eW (γ ⊗ₜ[R] d) = eW (d
        ⊗ₜ[R] γ) := rfl

/-- Compatible stage presentations identify the chart restriction with the
restriction of the tensor-stage rings. -/
private theorem stgHom_restriction
    (Δ : Type u) [CommRing Δ] [Algebra R Δ] (ρ : Γ →ₐ[R] Δ)
    (D : FGSubalgebra R A) (W Z : Type u) [CommRing W] [CommRing Z]
    [Algebra (↥D.1) W] [Algebra (↥D.1) Z]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) (eZ : ↥D.1 ⊗[R] Δ ≃ₐ[↥D.1] Z)
    (v : W →ₐ[↥D.1] Z)
    (hρ : ∀ (d : ↥D.1) (γ : Γ), v (eW (d ⊗ₜ[R] γ)) = eZ (d ⊗ₜ[R] ρ γ)) :
    v.toRingHom.comp (stgHom R A Γ D W eW) =
      (stgHom R A Δ D Z eZ).comp
        (Algebra.TensorProduct.map ρ (AlgHom.id R ↥D.1)).toRingHom := by
  refine Algebra.TensorProduct.ringHom_ext
    (R := R) (A := Γ) (B := ↥D.1) (C := Z) ?_ ?_
  · exact RingHom.ext fun γ => hρ (1 : ↥D.1) γ
  · exact RingHom.ext fun d => hρ d (1 : Γ)

/-- Compatibility of two tensor presentations determines the factorization of
 the vertex map through the stage map. Only the two tensor-ring generators are
 needed, so the statement applies equally to a chart and to its overlap. -/
theorem vtxHom_eq_comp_stgHom
    (D : FGSubalgebra R A) (W : Type u) [CommRing W] [Algebra (↥D.1) W]
    (eW : ↥D.1 ⊗[R] Γ ≃ₐ[↥D.1] W) (φ : W →+* U)
    (hφe : ∀ (d : ↥D.1) (γ : Γ), φ (eW (d ⊗ₜ[R] γ)) = eU ((d : A) ⊗ₜ[R] γ)) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    (vtxHom R A Γ U eU D).toRingHom = φ.comp (stgHom R A Γ D W eW) := by
  intro chartAlgebra
  refine Algebra.TensorProduct.ringHom_ext
    (R := R) (A := Γ) (B := ↥D.1) (C := U) ?_ ?_
  · exact RingHom.ext fun γ => (hφe (1 : ↥D.1) γ).symm
  · exact RingHom.ext fun d => (hφe d (1 : Γ)).symm

end VertexGeo

section AbstractSurj

open _root_.TwoChartCech
open _root_.AlgebraicGeometry.FGSubalgebra

section NativeChartGeneratorNotation
open scoped ChangeOfRings
open _root_.ModuleCat

/-- Restricting a tensor stage commutes with enlarging the finitely generated
base subalgebra. -/
private theorem tensorStage_restriction_natural
    (R A Γ Δ : Type u) [CommRing R] [CommRing A] [CommRing Γ] [CommRing Δ]
    [Algebra R A] [Algebra R Γ] [Algebra R Δ]
    (ρ : Γ →ₐ[R] Δ) (i j : FGSubalgebra R A) (h : i ≤ j) :
    (tensorStageMap R A Δ i j h).toRingHom.comp
        (Algebra.TensorProduct.map ρ (AlgHom.id R ↥i.1)).toRingHom =
      (Algebra.TensorProduct.map ρ (AlgHom.id R ↥j.1)).toRingHom.comp
        (tensorStageMap R A Γ i j h).toRingHom := by
  refine Algebra.TensorProduct.ringHom_ext
    (R := R) (A := Γ) (B := ↥i.1) (C := tensorStage R A Δ j) ?_ ?_
  · exact RingHom.ext fun γ => rfl
  · exact RingHom.ext fun d => rfl

/-- A tensor presentation compatible with a chart restriction gives the
corresponding commutative ring diagram from every finite stage to the limit. -/
private theorem tensorStage_presentation_restriction
    (R A Γ Δ U V : Type u) [CommRing R] [CommRing A] [CommRing Γ] [CommRing Δ]
    [CommRing U] [CommRing V] [Algebra R A] [Algebra R Γ] [Algebra R Δ]
    [Algebra A U] [Algebra A V]
    (ρ : Γ →ₐ[R] Δ) (eU : A ⊗[R] Γ ≃ₐ[A] U) (eV : A ⊗[R] Δ ≃ₐ[A] V)
    (v : U →ₐ[A] V)
    (hρ : ∀ (a : A) (γ : Γ), v (eU (a ⊗ₜ[R] γ)) = eV (a ⊗ₜ[R] ρ γ))
    (D : FGSubalgebra R A) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    let _ : Algebra Δ V := algebraOfPresent R A Δ V eV
    (vtxHom R A Δ V eV D).toRingHom.comp
        (Algebra.TensorProduct.map ρ (AlgHom.id R ↥D.1)).toRingHom =
      v.toRingHom.comp (vtxHom R A Γ U eU D).toRingHom := by
  intro chartAlgebra overlapAlgebra
  refine Algebra.TensorProduct.ringHom_ext
    (R := R) (A := Γ) (B := ↥D.1) (C := V) ?_ ?_
  · exact RingHom.ext fun γ => (hρ (1 : A) γ).symm
  · exact RingHom.ext fun d => (hρ (d : A) (1 : Γ)).symm

/-- Descend an invertible chart and construct its overlap realization from
its original tensor presentation and restriction law. -/
private theorem exists_invertible_chart_and_overlap
    (R A Γ U V : Type u) [CommRing R] [CommRing A] [CommRing Γ]
    [CommRing U] [CommRing V] [Algebra R A] [Algebra R Γ] [Algebra A U]
    (eU : A ⊗[R] Γ ≃ₐ[A] U) (v : U →+* V)
    {N O : Type w} [AddCommGroup N] [Module U N] [Module.Invertible U N]
    [AddCommGroup O] [Module V O]
    (rbc : let _ : Algebra U V := v.toAlgebra; V ⊗[U] N ≃ₗ[V] O) (r : N → O)
    (hrbc : let _ : Algebra U V := v.toAlgebra;
      ∀ n, rbc ((1 : V) ⊗ₜ[U] n) = r n) :
    let _ : Algebra Γ U := algebraOfPresent R A Γ U eU
    ∃ (i : FGSubalgebra R A) (P : ModuleCat.{u} (tensorStage R A Γ i)),
      Module.Invertible (tensorStage R A Γ i) P ∧
      Module.FinitePresentation (tensorStage R A Γ i) P ∧
      ∃ (I : (extendScalars (vtxHom R A Γ U eU i).toRingHom).obj P ≃ₗ[U] N)
        (J : (extendScalars v).obj
          ((extendScalars (vtxHom R A Γ U eU i).toRingHom).obj P) ≃ₗ[V] O),
        ∀ m : (extendScalars (vtxHom R A Γ U eU i).toRingHom).obj P,
          J ((extendRestrictScalarsAdj v).unit.app _ m) = r (I m) := by
  intro chartAlgebra
  classical
  have : IsDirectedOrder (FGSubalgebra R A) := ⟨IsDirected.directed⟩
  obtain ⟨i, K, _, _, hK, ⟨Iraw⟩⟩ :=
    Module.IsDirectLimit.exists_invertible_linearEquiv_baseChange
      (tensorStage R A Γ) (fun i j h => tensorStageMap R A Γ i j h)
      U (vtxHom R A Γ U eU) (vtxHom_comp R A Γ U eU)
      (vtxHom_surj R A Γ U eU) (vtxHom_zero R A Γ U eU) N
  have hfp : Module.FinitePresentation (tensorStage R A Γ i) K :=
    Module.finitePresentation_of_projective (tensorStage R A Γ i) K
  let P : ModuleCat.{u} (tensorStage R A Γ i) := ModuleCat.of _ K
  let M : ModuleCat.{u} U :=
    (extendScalars (vtxHom R A Γ U eU i).toRingHom).obj P
  let I : M ≃ₗ[U] N := by
    let : Algebra (tensorStage R A Γ i) U := (vtxHom R A Γ U eU i).toRingHom.toAlgebra
    exact Iraw
  obtain ⟨J, hJ⟩ := exists_scalarExtension_realization v M I rbc r hrbc
  exact ⟨i, P, hK, hfp, I, J, hJ⟩

theorem exists_fg_gluingData
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (𝒰 : Cover.{u, u} R) (UA : Cover.{u, u} A) (T : Sections.{u, u, w} UA)
    [Module.Invertible UA.A0 T.M0] [Module.Invertible UA.A1 T.M1]
    (eU0 : A ⊗[R] 𝒰.A0 ≃ₐ[A] UA.A0) (eU1 : A ⊗[R] 𝒰.A1 ≃ₐ[A] UA.A1) (eU01 : A ⊗[R] 𝒰.A01 ≃ₐ[A]
        UA.A01)
    (hρU0 : ∀ (a : A) (γ : 𝒰.A0), UA.ρ0 (eU0 (a ⊗ₜ[R] γ)) = eU01 (a ⊗ₜ[R] 𝒰.ρ0 γ))
    (hρU1 : ∀ (a : A) (γ : 𝒰.A1), UA.ρ1 (eU1 (a ⊗ₜ[R] γ)) = eU01 (a ⊗ₜ[R] 𝒰.ρ1 γ))
    (rbc0 :
      let _ : Algebra UA.A0 UA.A01 := UA.ρ0.toRingHom.toAlgebra
      UA.A01 ⊗[UA.A0] T.M0 ≃ₗ[UA.A01] T.M01)
    (hrbc0 :
      let _ : Algebra UA.A0 UA.A01 := UA.ρ0.toRingHom.toAlgebra
      ∀ m, rbc0 ((1 : UA.A01) ⊗ₜ[UA.A0] m) = T.r0 m)
    (rbc1 :
      let _ : Algebra UA.A1 UA.A01 := UA.ρ1.toRingHom.toAlgebra
      UA.A01 ⊗[UA.A1] T.M1 ≃ₗ[UA.A01] T.M01)
    (hrbc1 :
      let _ : Algebra UA.A1 UA.A01 := UA.ρ1.toRingHom.toAlgebra
      ∀ m, rbc1 ((1 : UA.A01) ⊗ₜ[UA.A1] m) = T.r1 m)
    (V : ∀ D : FGSubalgebra R A, Cover.{u, u} ↥D.1)
    (eV0 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A0 ≃ₐ[↥D.1] (V D).A0)
    (eV1 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A1 ≃ₐ[↥D.1] (V D).A1)
    (eV01 : ∀ D : FGSubalgebra R A, ↥D.1 ⊗[R] 𝒰.A01 ≃ₐ[↥D.1] (V D).A01)
    (hρV0 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A0), (V D).ρ0 (eV0 D (d ⊗ₜ[R] γ)) = eV01 D
        (d ⊗ₜ[R] 𝒰.ρ0 γ))
    (hρV1 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A1), (V D).ρ1 (eV1 D (d ⊗ₜ[R] γ)) = eV01 D
        (d ⊗ₜ[R] 𝒰.ρ1 γ))
    (φ0 : ∀ D : FGSubalgebra R A, (V D).A0 →+* UA.A0) (φ1 : ∀ D : FGSubalgebra R A, (V D).A1 →+*
        UA.A1)
    (φ01 : ∀ D : FGSubalgebra R A, (V D).A01 →+* UA.A01)
    (eφ0 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A0 ≃ₐ[A] UA.A0)
    (heφ0 : ∀ (D : FGSubalgebra R A) (s : (V D).A0), eφ0 D ((1 : A) ⊗ₜ[↥D.1] s) = φ0 D s)
    (eφ1 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A1 ≃ₐ[A] UA.A1)
    (heφ1 : ∀ (D : FGSubalgebra R A) (s : (V D).A1), eφ1 D ((1 : A) ⊗ₜ[↥D.1] s) = φ1 D s)
    (eφ01 : ∀ D : FGSubalgebra R A, A ⊗[↥D.1] (V D).A01 ≃ₐ[A] UA.A01)
    (heφ01 : ∀ (D : FGSubalgebra R A) (s : (V D).A01), eφ01 D ((1 : A) ⊗ₜ[↥D.1] s) = φ01 D s)
    (hφρ0 : ∀ (D : FGSubalgebra R A) (s : (V D).A0), φ01 D ((V D).ρ0 s) = UA.ρ0 (φ0 D s))
    (hφρ1 : ∀ (D : FGSubalgebra R A) (s : (V D).A1), φ01 D ((V D).ρ1 s) = UA.ρ1 (φ1 D s))
    (hφe0 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A0), φ0 D (eV0 D (d ⊗ₜ[R] γ)) = eU0 ((d :
        A) ⊗ₜ[R] γ))
    (hφe1 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A1), φ1 D (eV1 D (d ⊗ₜ[R] γ)) = eU1 ((d :
        A) ⊗ₜ[R] γ))
    (hφe01 : ∀ (D : FGSubalgebra R A) (d : ↥D.1) (γ : 𝒰.A01), φ01 D (eV01 D (d ⊗ₜ[R] γ)) = eU01
        ((d : A) ⊗ₜ[R] γ)) :
    ∃ (D : FGSubalgebra R A)
      (P0 : Type u) (_ : AddCommGroup P0) (_ : Module (V D).A0 P0) (_ : Module.Finite (V D).A0 P0)
      (_ : Module.Projective (V D).A0 P0)
      (P1 : Type u) (_ : AddCommGroup P1) (_ : Module (V D).A1 P1) (_ : Module.Finite (V D).A1 P1)
      (_ : Module.Projective (V D).A1 P1)
      (_ : ∀ (K : Type u) [Field K] [Algebra (V D).A0 K], Module.finrank K (K ⊗[(V D).A0] P0) = 1)
      (_ : ∀ (K : Type u) [Field K] [Algebra (V D).A1 K], Module.finrank K (K ⊗[(V D).A1] P1) = 1)
      (σ :
        let _ : Algebra (V D).A0 (V D).A01 := (V D).ρ0.toRingHom.toAlgebra
        let _ : Algebra (V D).A1 (V D).A01 := (V D).ρ1.toRingHom.toAlgebra
        (V D).A01 ⊗[(V D).A0] P0 ≃ₗ[(V D).A01] (V D).A01 ⊗[(V D).A1] P1),
      ∀ (S : Sections.{u, u, w} (V D)) (e0 : S.M0 ≃ₗ[(V D).A0] P0)
        (e1 : S.M1 ≃ₗ[(V D).A1] P1)
        (e01 :
          let _ : Algebra (V D).A0 (V D).A01 := (V D).ρ0.toRingHom.toAlgebra
          S.M01 ≃ₗ[(V D).A01] (V D).A01 ⊗[(V D).A0] P0),
        (let _ : Algebra (V D).A0 (V D).A01 := (V D).ρ0.toRingHom.toAlgebra
          ∀ m, e01 (S.r0 m) = (1 : (V D).A01) ⊗ₜ[(V D).A0] e0 m) →
        (let _ : Algebra (V D).A0 (V D).A01 := (V D).ρ0.toRingHom.toAlgebra
         let _ : Algebra (V D).A1 (V D).A01 := (V D).ρ1.toRingHom.toAlgebra
          ∀ m, σ (e01 (S.r1 m)) = (1 : (V D).A01) ⊗ₜ[(V D).A1] e1 m) →
        Nonempty (ChartBC (k := ↥D.1) (A' := A) (φ0 D) (φ1 D) (φ01 D) S T) := by
  classical
  have : IsDirectedOrder (FGSubalgebra R A) := ⟨IsDirected.directed⟩
  let B0 : FGSubalgebra R A → Type u := tensorStage R A 𝒰.A0
  let B1 : FGSubalgebra R A → Type u := tensorStage R A 𝒰.A1
  let C : FGSubalgebra R A → Type u := tensorStage R A 𝒰.A01
  let tau0 : ∀ i j : FGSubalgebra R A, i ≤ j → B0 i →+* B0 j :=
    fun i j h => (tensorStageMap R A 𝒰.A0 i j h).toRingHom
  let tau1 : ∀ i j : FGSubalgebra R A, i ≤ j → B1 i →+* B1 j :=
    fun i j h => (tensorStageMap R A 𝒰.A1 i j h).toRingHom
  let tauC : ∀ i j : FGSubalgebra R A, i ≤ j → C i →+* C j :=
    fun i j h => (tensorStageMap R A 𝒰.A01 i j h).toRingHom
  let g0 : ∀ D : FGSubalgebra R A, B0 D →+* UA.A0 := by
    let : Algebra 𝒰.A0 UA.A0 := algebraOfPresent R A 𝒰.A0 UA.A0 eU0
    exact fun D => (vtxHom R A 𝒰.A0 UA.A0 eU0 D).toRingHom
  let g1 : ∀ D : FGSubalgebra R A, B1 D →+* UA.A1 := by
    let : Algebra 𝒰.A1 UA.A1 := algebraOfPresent R A 𝒰.A1 UA.A1 eU1
    exact fun D => (vtxHom R A 𝒰.A1 UA.A1 eU1 D).toRingHom
  let gC : ∀ D : FGSubalgebra R A, C D →+* UA.A01 := by
    let : Algebra 𝒰.A01 UA.A01 := algebraOfPresent R A 𝒰.A01 UA.A01 eU01
    exact fun D => (vtxHom R A 𝒰.A01 UA.A01 eU01 D).toRingHom
  let res0 : ∀ D : FGSubalgebra R A, B0 D →+* C D := fun D =>
    (Algebra.TensorProduct.map 𝒰.ρ0 (AlgHom.id R ↥D.1)).toRingHom
  let res1 : ∀ D : FGSubalgebra R A, B1 D →+* C D := fun D =>
    (Algebra.TensorProduct.map 𝒰.ρ1 (AlgHom.id R ↥D.1)).toRingHom
  have hg0 : ∀ i j (h : i ≤ j), (g0 j).comp (tau0 i j h) = g0 i := by
    intro i j h
    let : Algebra 𝒰.A0 UA.A0 := algebraOfPresent R A 𝒰.A0 UA.A0 eU0
    exact congrArg (fun f : tensorStage R A 𝒰.A0 i →ₐ[𝒰.A0] UA.A0 => f.toRingHom)
      (vtxHom_comp R A 𝒰.A0 UA.A0 eU0 i j h)
  have hg1 : ∀ i j (h : i ≤ j), (g1 j).comp (tau1 i j h) = g1 i := by
    intro i j h
    let : Algebra 𝒰.A1 UA.A1 := algebraOfPresent R A 𝒰.A1 UA.A1 eU1
    exact congrArg (fun f : tensorStage R A 𝒰.A1 i →ₐ[𝒰.A1] UA.A1 => f.toRingHom)
      (vtxHom_comp R A 𝒰.A1 UA.A1 eU1 i j h)
  have hgC : ∀ i j (h : i ≤ j), (gC j).comp (tauC i j h) = gC i := by
    intro i j h
    let : Algebra 𝒰.A01 UA.A01 := algebraOfPresent R A 𝒰.A01 UA.A01 eU01
    exact congrArg (fun f : tensorStage R A 𝒰.A01 i →ₐ[𝒰.A01] UA.A01 => f.toRingHom)
      (vtxHom_comp R A 𝒰.A01 UA.A01 eU01 i j h)
  have hres0 : ∀ i j (h : i ≤ j),
      (tauC i j h).comp (res0 i) = (res0 j).comp (tau0 i j h) := by
    exact fun i j h => tensorStage_restriction_natural R A 𝒰.A0 𝒰.A01 𝒰.ρ0 i j h
  have hlim0 : ∀ D, (gC D).comp (res0 D) = UA.ρ0.toRingHom.comp (g0 D) := by
    exact fun D => tensorStage_presentation_restriction R A 𝒰.A0 𝒰.A01
      UA.A0 UA.A01 𝒰.ρ0 eU0 eU01 UA.ρ0 hρU0 D
  obtain ⟨i0, oldP0, hInv0, hFP0, oldI0Native, smallOverlap0, hSmallOverlap0⟩ :=
    exists_invertible_chart_and_overlap R A 𝒰.A0 UA.A0 UA.A01 eU0
      UA.ρ0.toRingHom rbc0 T.r0 hrbc0
  have : Module.Invertible (tensorStage R A 𝒰.A0 i0) oldP0 := hInv0
  let smallM0 : ModuleCat.{u} UA.A0 := (extendScalars (g0 i0)).obj oldP0
  have : Module.FinitePresentation (B0 i0) oldP0 := hFP0
  have hres1 : ∀ i j (h : i ≤ j),
      (tauC i j h).comp (res1 i) = (res1 j).comp (tau1 i j h) := by
    exact fun i j h => tensorStage_restriction_natural R A 𝒰.A1 𝒰.A01 𝒰.ρ1 i j h
  have hlim1 : ∀ D, (gC D).comp (res1 D) = UA.ρ1.toRingHom.comp (g1 D) := by
    exact fun D => tensorStage_presentation_restriction R A 𝒰.A1 𝒰.A01
      UA.A1 UA.A01 𝒰.ρ1 eU1 eU01 UA.ρ1 hρU1 D
  obtain ⟨i1, oldP1, hInv1, hFP1, oldI1Native, smallOverlap1, hSmallOverlap1⟩ :=
    exists_invertible_chart_and_overlap R A 𝒰.A1 UA.A1 UA.A01 eU1
      UA.ρ1.toRingHom rbc1 T.r1 hrbc1
  have : Module.Invertible (tensorStage R A 𝒰.A1 i1) oldP1 := hInv1
  let smallM1 : ModuleCat.{u} UA.A1 := (extendScalars (g1 i1)).obj oldP1
  have : Module.FinitePresentation (B1 i1) oldP1 := hFP1
  let sigmaLimit : (extendScalars UA.ρ0.toRingHom).obj smallM0 ≅
      (extendScalars UA.ρ1.toRingHom).obj smallM1 :=
    (smallOverlap0 ≪≫ₗ smallOverlap1.symm).toModuleIso
  have hSigmaLimit : ∀ z : (extendScalars UA.ρ0.toRingHom).obj smallM0,
      smallOverlap1 (sigmaLimit.hom z) = smallOverlap0 z :=
    fun z => smallOverlap1.apply_symm_apply (smallOverlap0 z)
  obtain ⟨D, h0, h1, E0, E1, F0, F1, stageIso, hF0unit, hF1unit, hreal⟩ :=
      exists_common_stage_clutching
    B0 B1 C tau0 tau1 tauC UA.A0 UA.A1 UA.A01 g0 g1 gC hg0 hg1 hgC
    (vtxHom_surj R A 𝒰.A01 UA.A01 eU01)
    (vtxHom_zero R A 𝒰.A01 UA.A01 eU01)
    res0 res1 hres0 hres1 UA.ρ0.toRingHom UA.ρ1.toRingHom hlim0 hlim1
    i0 i1 oldP0 oldP1 sigmaLimit
  let t0 : B0 D →+* (V D).A0 := stgHom R A 𝒰.A0 D (V D).A0 (eV0 D)
  let t1 : B1 D →+* (V D).A1 := stgHom R A 𝒰.A1 D (V D).A1 (eV1 D)
  let tC : C D →+* (V D).A01 := stgHom R A 𝒰.A01 D (V D).A01 (eV01 D)
  have hCompat0 : g0 D = (φ0 D).comp t0 :=
    vtxHom_eq_comp_stgHom R A 𝒰.A0 UA.A0 eU0 D (V D).A0
      (eV0 D) (φ0 D) (hφe0 D)
  have hCompat1 : g1 D = (φ1 D).comp t1 :=
    vtxHom_eq_comp_stgHom R A 𝒰.A1 UA.A1 eU1 D (V D).A1
      (eV1 D) (φ1 D) (hφe1 D)
  have hCompatC : gC D = (φ01 D).comp tC :=
    vtxHom_eq_comp_stgHom R A 𝒰.A01 UA.A01 eU01 D (V D).A01
      (eV01 D) (φ01 D) (hφe01 D)
  let L0 : ModuleCat.{u} (B0 D) := (extendScalars (tau0 i0 D h0)).obj oldP0
  let Q0 : ModuleCat.{u} (C D) := (extendScalars (res0 D)).obj L0
  have : Module.Invertible (B0 D) L0 :=
    invertible_extendScalars_of_invertible (tau0 i0 D h0) oldP0
  obtain ⟨newI0, Xi0, Xi0Native, hXi0real, hXi0Native, hXi0gen⟩ :=
    exists_algebraTensor_realization_of_maps (g0 D) (res0 D) (gC D) UA.ρ0.toRingHom
      L0 smallM0 E0 F0 oldI0Native smallOverlap0 T.r0 hF0unit hSmallOverlap0
  let L1 : ModuleCat.{u} (B1 D) := (extendScalars (tau1 i1 D h1)).obj oldP1
  let Q1 : ModuleCat.{u} (C D) := (extendScalars (res1 D)).obj L1
  have : Module.Invertible (B1 D) L1 :=
    invertible_extendScalars_of_invertible (tau1 i1 D h1) oldP1
  obtain ⟨newI1, Xi1, Xi1Native, hXi1real, hXi1Native, hXi1gen⟩ :=
    exists_algebraTensor_realization_of_maps (g1 D) (res1 D) (gC D) UA.ρ1.toRingHom
      L1 smallM1 E1 F1 oldI1Native smallOverlap1 T.r1 hF1unit hSmallOverlap1
  let P0 : ModuleCat.{u} (V D).A0 := algebraTensorObj t0 L0
  have hSquare0 : (V D).ρ0.toRingHom.comp t0 = tC.comp (res0 D) := by
    exact stgHom_restriction R A 𝒰.A0 𝒰.A01 𝒰.ρ0 D (V D).A0 (V D).A01
      (eV0 D) (eV01 D) (V D).ρ0 (hρV0 D)
  let P1 : ModuleCat.{u} (V D).A1 := algebraTensorObj t1 L1
  have hSquare1 : (V D).ρ1.toRingHom.comp t1 = tC.comp (res1 D) := by
    exact stgHom_restriction R A 𝒰.A1 𝒰.A01 𝒰.ρ1 D (V D).A1 (V D).A01
      (eV1 D) (eV01 D) (V D).ρ1 (hρV1 D)
  let algB0V0 : Algebra (B0 D) (V D).A0 := t0.toAlgebra
  let algB1V1 : Algebra (B1 D) (V D).A1 := t1.toAlgebra
  let algB0U0 : Algebra (B0 D) UA.A0 := (g0 D).toAlgebra
  let algB1U1 : Algebra (B1 D) UA.A1 := (g1 D).toAlgebra
  let algV0V01 : Algebra (V D).A0 (V D).A01 := (V D).ρ0.toRingHom.toAlgebra
  let algV1V01 : Algebra (V D).A1 (V D).A01 := (V D).ρ1.toRingHom.toAlgebra
  let algCV01 : Algebra (C D) (V D).A01 := tC.toAlgebra
  let algCU01 : Algebra (C D) UA.A01 := (gC D).toAlgebra
  have : Module.Invertible (V D).A0 P0 :=
    invertible_algebraTensorObj_of_invertible t0 L0
  have : Module.Invertible (V D).A1 P1 :=
    invertible_algebraTensorObj_of_invertible t1 L1
  obtain ⟨kappa0, kappa1, sigmaV, hKappa0, hKappa1, hKappaSigma⟩ :=
    exists_algebraTensor_clutching_of_commuting_squares t0 t1 (res0 D) (res1 D)
      (V D).ρ0.toRingHom (V D).ρ1.toRingHom tC hSquare0 hSquare1 L0 L1 stageIso
  let sigmaV' : (V D).A01 ⊗[C D] Q0 ≃ₗ[(V D).A01] (V D).A01 ⊗[C D] Q1 :=
    LinearEquiv.baseChange (C D) (V D).A01 Q0 Q1 stageIso.toLinearEquiv
  change ∀ z : (V D).A01 ⊗[(V D).A0] P0,
    kappa1 (sigmaV z) = sigmaV' (kappa0 z) at hKappaSigma
  let sigmaU : UA.A01 ⊗[C D] Q0 ≃ₗ[UA.A01] UA.A01 ⊗[C D] Q1 :=
    LinearEquiv.baseChange (C D) UA.A01 Q0 Q1 stageIso.toLinearEquiv
  have hXiSigmaNative := realization_extendScalars_compat (gC D) Q0 Q1
    ((extendScalars UA.ρ0.toRingHom).obj smallM0) ((extendScalars UA.ρ1.toRingHom).obj smallM1)
    stageIso F0 F1 sigmaLimit Xi0Native Xi1Native smallOverlap0 smallOverlap1
    hXi0real hXi1real hSigmaLimit hreal
  have hXiSigma : ∀ z : UA.A01 ⊗[C D] Q0, Xi1 (sigmaU z) = Xi0 z := by
    exact algebraTensor_realization_baseChange_compat (gC D) Q0 Q1 stageIso
      Xi0Native Xi1Native Xi0 Xi1 hXi0Native hXi1Native hXiSigmaNative
  have : SMulCommClass (B0 D) ↥D.1 (V D).A0 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (B1 D) ↥D.1 (V D).A1 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (V D).A0 ↥D.1 (V D).A01 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (V D).A1 ↥D.1 (V D).A01 :=
    smulCommClass_of_algebras (V D).A1 ↥D.1 (V D).A01
  have : SMulCommClass (B0 D) A UA.A0 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (B1 D) A UA.A1 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (C D) ↥D.1 (V D).A01 := smulCommClass_of_algebras _ _ _
  have : SMulCommClass (C D) A UA.A01 := smulCommClass_of_algebras _ _ _
  refine ⟨D, (P0 : Type u), inferInstance, inferInstance, inferInstance, inferInstance,
    (P1 : Type u), inferInstance, inferInstance, inferInstance, inferInstance,
    finrank_baseChange_eq_one_of_invertible (A := (V D).A0) (P0 : Type u),
    finrank_baseChange_eq_one_of_invertible (A := (V D).A1) (P1 : Type u),
    sigmaV, fun S e0 e1 e01 hC0 hC1 => ?_⟩
  obtain ⟨Z0', hZ0', hZ0's⟩ := exists_presentEquiv ↥D.1 A (V D).A0 UA.A0 (B0 D) L0
    (φ0 D) (eφ0 D) (heφ0 D) (fun b => RingHom.congr_fun hCompat0 b)
  obtain ⟨Z1', hZ1', hZ1's⟩ := exists_presentEquiv ↥D.1 A (V D).A1 UA.A1 (B1 D) L1
    (φ1 D) (eφ1 D) (heφ1 D) (fun b => RingHom.congr_fun hCompat1 b)
  obtain ⟨present0, present1, hPresent0, hPresent0s, hPresent1, hPresentSigma⟩ :=
    exists_presentEquivs_natural ↥D.1 A (V D).A01 UA.A01 (C D) Q0 Q1
      (φ01 D) (eφ01 D) (heφ01 D) (fun b => RingHom.congr_fun hCompatC b) stageIso.toLinearEquiv
  obtain ⟨H0, hH0, hH0s⟩ := TensorProduct.exists_realized_tensorPresentation_with_scalar
    ↥D.1 A UA.A0 (S := (V D).A0) (P := (V D).A0 ⊗[B0 D] L0)
    (Q := UA.A0 ⊗[B0 D] L0) (N := T.M0) (φ0 D) Z0'
    (show UA.A0 ⊗[B0 D] L0 ≃ₗ[UA.A0] T.M0 from newI0) (hZ0's (1 : A))
  obtain ⟨Z0, hZ0, hZ0s⟩ := TensorProduct.exists_coordinate_realization_with_scalar
    ↥D.1 A (V D).A0 (M := S.M0) (P := (V D).A0 ⊗[B0 D] L0)
    (N := T.M0) (U := UA.A0) (X := UA.A0 ⊗[B0 D] L0)
    (φ0 D) (show S.M0 ≃ₗ[(V D).A0] (V D).A0 ⊗[B0 D] L0 from e0) H0 Z0' newI0 hH0 hH0s
  obtain ⟨H1, hH1, hH1s⟩ := TensorProduct.exists_realized_tensorPresentation_with_scalar
    ↥D.1 A UA.A1 (S := (V D).A1) (P := (V D).A1 ⊗[B1 D] L1)
    (Q := UA.A1 ⊗[B1 D] L1) (N := T.M1) (φ1 D) Z1'
    (show UA.A1 ⊗[B1 D] L1 ≃ₗ[UA.A1] T.M1 from newI1) (hZ1's (1 : A))
  obtain ⟨Z1, hZ1, hZ1s⟩ := TensorProduct.exists_coordinate_realization_with_scalar
    ↥D.1 A (V D).A1 (M := S.M1) (P := (V D).A1 ⊗[B1 D] L1)
    (N := T.M1) (U := UA.A1) (X := UA.A1 ⊗[B1 D] L1)
    (φ1 D) (show S.M1 ≃ₗ[(V D).A1] (V D).A1 ⊗[B1 D] L1 from e1) H1 Z1' newI1 hH1 hH1s
  obtain ⟨H01, hH01, hH01s⟩ := TensorProduct.exists_realized_tensorPresentation_with_scalar
    ↥D.1 A UA.A01 (S := (V D).A01) (P := (V D).A01 ⊗[C D] Q0)
    (Q := UA.A01 ⊗[C D] Q0) (N := T.M01) (φ01 D) present0
    (show UA.A01 ⊗[C D] Q0 ≃ₗ[UA.A01] T.M01 from Xi0) (hPresent0s (1 : A))
  obtain ⟨Z01, hZ01, hZ01s⟩ := TensorProduct.exists_coordinate_realization_with_scalar
    ↥D.1 A (V D).A01 (M := S.M01) (P := (V D).A01 ⊗[C D] Q0)
    (N := T.M01) (U := UA.A01) (X := UA.A01 ⊗[C D] Q0)
    (φ01 D) (e01 ≪≫ₗ kappa0) H01 present0 Xi0 hH01 hH01s
  simp only [LinearEquiv.trans_apply] at hZ01
  have htransition := TensorProduct.realized_presentation_coordinate_transition
    ↥D.1 A (V D).A01 (C D) Q0 Q1 stageIso.toLinearEquiv
    kappa0 kappa1 sigmaV present0 present1 sigmaU Xi0 Xi1
    hKappaSigma hPresentSigma hXiSigma
  have hZ01_1 : ∀ (a : A) (m : S.M01),
      Z01 (a ⊗ₜ[↥D.1] m) = Xi1 (present1 (a ⊗ₜ[↥D.1] kappa1 (sigmaV (e01 m)))) := by
    intro a m
    exact (hZ01 a m).trans (htransition a (e01 m)).symm
  refine ⟨{ β0 := Z0, β1 := Z1, β01 := Z01, hr0 := ?_, hr1 := ?_, hs0 := hZ0s, hs1 := hZ1s, hs01
      := hZ01s }⟩
  · exact TensorProduct.baseChange_square_of_native_chart_coordinates
      (k := ↥D.1) (A := A) (B := B0 D) (J := (V D).A0)
      (C := C D) (D := (V D).A01) (U := UA.A0) (V := UA.A01)
      (algBJ := algB0V0) (algBU := algB0U0)
      (algJD := algV0V01) (algCD := algCV01) (algCV := algCU01)
      (X := L0) (Q := Q0) (M := S.M0) (N := S.M01)
      (T0 := T.M0) (T1 := T.M01)
      e0.toAddEquiv S.r0 T.r0 Z0 Z01 e01 kappa0 newI0 Xi0
      (fun p : (V D).A0 ⊗[B0 D] L0 => Z0' ((1 : A) ⊗ₜ[↥D.1] p))
      (fun q : (V D).A01 ⊗[C D] Q0 => present0 ((1 : A) ⊗ₜ[↥D.1] q))
      (fun x : L0 =>
        (show Q0 from (extendRestrictScalarsAdj (res0 D)).unit.app L0 x))
      (V D).ρ0.toRingHom UA.ρ0.toRingHom (φ0 D) (φ01 D)
      hKappa0 (hPresent0 (1 : A)) hXi0gen (hZ0' (1 : A))
      (hZ01 (1 : A)) (hZ0 (1 : A)) hC0 T.r0_smul (hφρ0 D)
  · exact TensorProduct.baseChange_square_of_native_chart_coordinates
      (k := ↥D.1) (A := A) (B := B1 D) (J := (V D).A1)
      (C := C D) (D := (V D).A01) (U := UA.A1) (V := UA.A01)
      (algBJ := algB1V1) (algBU := algB1U1)
      (algJD := algV1V01) (algCD := algCV01) (algCV := algCU01)
      (X := L1) (Q := Q1) (M := S.M1) (N := S.M01)
      (T0 := T.M1) (T1 := T.M01)
      e1.toAddEquiv S.r1 T.r1 Z1 Z01 (fun n : S.M01 => sigmaV (e01 n)) kappa1 newI1 Xi1
      (fun p : (V D).A1 ⊗[B1 D] L1 => Z1' ((1 : A) ⊗ₜ[↥D.1] p))
      (fun q : (V D).A01 ⊗[C D] Q1 => present1 ((1 : A) ⊗ₜ[↥D.1] q))
      (fun x : L1 =>
        (show Q1 from (extendRestrictScalarsAdj (res1 D)).unit.app L1 x))
      (V D).ρ1.toRingHom UA.ρ1.toRingHom (φ1 D) (φ01 D)
      hKappa1 (hPresent1 (1 : A)) hXi1gen (hZ1' (1 : A))
      (hZ01_1 (1 : A)) (hZ1 (1 : A)) hC1 T.r1_smul (hφρ1 D)

end NativeChartGeneratorNotation

end AbstractSurj

section GeoDict

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.TwoChartCech

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of
    R))


theorem cover_ρ0_present (B : Type u) [CommRing B] [Algebra R B]
    (e0 : B ⊗[R] (𝒱.cover c).A0 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R
        B))).A0)
    (e01 : B ⊗[R] (𝒱.cover c).A01 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R
        B))).A01)
    (he0 : ∀ s, e0 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app 𝒱.U0).hom s)
    (he01 : ∀ s, e01 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓
        𝒱.U1)).hom s)
    (b : B) (γ : (𝒱.cover c).A0) :
    ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ0 (e0 (b ⊗ₜ[R] γ)) = e01 (b
        ⊗ₜ[R] (𝒱.cover c).ρ0 γ) := by
  have hnat := Scheme.Hom.app_apply_map (Limits.pullback.fst c (specMap R B))
    (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) (show Γ(C, 𝒱.U0) from γ)
  change
    ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓ 𝒱.U1)).hom ((𝒱.cover c).ρ0 γ) =
      ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ0
        (((Limits.pullback.fst c (specMap R B)).app 𝒱.U0).hom γ) at hnat
  rw [show b ⊗ₜ[R] γ = b • ((1 : B) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show b ⊗ₜ[R] (𝒱.cover c).ρ0 γ = b • ((1 : B) ⊗ₜ[R] (𝒱.cover c).ρ0 γ) by rw
        [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, map_smul, he0, he01, hnat]

theorem cover_ρ1_present (B : Type u) [CommRing B] [Algebra R B]
    (e1 : B ⊗[R] (𝒱.cover c).A1 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R
        B))).A1)
    (e01 : B ⊗[R] (𝒱.cover c).A01 ≃ₐ[B] ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R
        B))).A01)
    (he1 : ∀ s, e1 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app 𝒱.U1).hom s)
    (he01 : ∀ s, e01 ((1 : B) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓
        𝒱.U1)).hom s)
    (b : B) (γ : (𝒱.cover c).A1) :
    ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ1 (e1 (b ⊗ₜ[R] γ)) = e01 (b
        ⊗ₜ[R] (𝒱.cover c).ρ1 γ) := by
  have hnat := Scheme.Hom.app_apply_map (Limits.pullback.fst c (specMap R B))
    (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) (show Γ(C, 𝒱.U1) from γ)
  change
    ((Limits.pullback.fst c (specMap R B)).app (𝒱.U0 ⊓ 𝒱.U1)).hom ((𝒱.cover c).ρ1 γ) =
      ((𝒱.pullback c B).cover (Limits.pullback.snd c (specMap R B))).ρ1
        (((Limits.pullback.fst c (specMap R B)).app 𝒱.U1).hom γ) at hnat
  rw [show b ⊗ₜ[R] γ = b • ((1 : B) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    show b ⊗ₜ[R] (𝒱.cover c).ρ1 γ = b • ((1 : B) ⊗ₜ[R] (𝒱.cover c).ρ1 γ) by rw
        [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, map_smul, map_smul, he1, he01, hnat]

variable (A : Type u) [CommRing A] [Algebra R A] (D : Subalgebra R A)

/-- The ring map from first chart sections at a finite stage to the limit chart sections. -/
noncomputable abbrev φU0 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE (𝒱.pullback c
      ↥D).U0
    (𝒱.pullback c A).U0 (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D
        A))).ge).hom
/-- The ring map from second chart sections at a finite stage to the limit chart sections. -/
noncomputable abbrev φU1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE (𝒱.pullback c
      ↥D).U1
    (𝒱.pullback c A).U1 (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D
        A))).ge).hom
/-- The ring map from overlap sections at a finite stage to the limit overlap sections. -/
noncomputable abbrev φU01 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01 →+*
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01 :=
  ((RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).appLE
    ((𝒱.pullback c ↥D).U0 ⊓ (𝒱.pullback c ↥D).U1) ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1)
    (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge).hom

theorem φU01_ρ0 (s : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0) :
    φU01 𝒱 c A D (((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).ρ0 s) =
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).ρ0 (φU0 𝒱 c A D s) := by
  rw [cover_ρ0_apply, cover_ρ0_apply]
  exact Scheme.Hom.appLE_apply_map _ _ _ inf_le_left inf_le_left s

theorem φU01_ρ1 (s : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1) :
    φU01 𝒱 c A D (((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).ρ1 s) =
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).ρ1 (φU1 𝒱 c A D s) := by
  rw [cover_ρ1_apply, cover_ρ1_apply]
  exact Scheme.Hom.appLE_apply_map _ _ _ inf_le_right inf_le_right s

theorem φU0_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A0 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R
        ↥D))).A0)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U0).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A0 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R
        A))).A0)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app 𝒱.U0).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A0 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU0 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A0) :
    φU0 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by
  have hsc : φU0 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
        smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R
          ↥D))).A0)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]
  have hfn : φU0 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U0).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app 𝒱.U0).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) (𝒱.U0) ((𝒱.pullback c
          A).U0)
      (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul',
        smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA]
  change φU0 𝒱 c A D (algebraMap ↥D _ d * _) = algebraMap A _ (d : A) * _
  exact ((φU0 𝒱 c A D).map_mul _ _).trans
    (congrArg₂ (fun x y : ((𝒱.pullback c A).cover
      (Limits.pullback.snd c (specMap R A))).A0 => x * y) hsc hfn)

theorem φU1_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A1 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R
        ↥D))).A1)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U1).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A1 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R
        A))).A1)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app 𝒱.U1).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A1 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU1 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A1) :
    φU1 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by
  have hsc : φU1 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
        smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R
          ↥D))).A1)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]
  have hfn : φU1 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app 𝒱.U1).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app 𝒱.U1).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) (𝒱.U1) ((𝒱.pullback c
          A).U1)
      (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul',
        smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA]
  change φU1 𝒱 c A D (algebraMap ↥D _ d * _) = algebraMap A _ (d : A) * _
  exact ((φU1 𝒱 c A D).map_mul _ _).trans
    (congrArg₂ (fun x y : ((𝒱.pullback c A).cover
      (Limits.pullback.snd c (specMap R A))).A1 => x * y) hsc hfn)

theorem φU01_present
    (eD : ↥D ⊗[R] (𝒱.cover c).A01 ≃ₐ[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap
        R ↥D))).A01)
    (heD : ∀ s, eD ((1 : ↥D) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R ↥D)).app (𝒱.U0 ⊓
        𝒱.U1)).hom s)
    (eA : A ⊗[R] (𝒱.cover c).A01 ≃ₐ[A] ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R
        A))).A01)
    (heA : ∀ s, eA ((1 : A) ⊗ₜ[R] s) = ((Limits.pullback.fst c (specMap R A)).app (𝒱.U0 ⊓
        𝒱.U1)).hom s)
    (eφ : A ⊗[↥D] ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R ↥D))).A01 ≃ₐ[A]
      ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A01)
    (heφ : ∀ s, eφ ((1 : A) ⊗ₜ[↥D] s) = φU01 𝒱 c A D s)
    (d : ↥D) (γ : (𝒱.cover c).A01) :
    φU01 𝒱 c A D (eD (d ⊗ₜ[R] γ)) = eA ((d : A) ⊗ₜ[R] γ) := by
  have hsc : φU01 𝒱 c A D (algebraMap ↥D _ d) = algebraMap A _ (d : A) := by
    rw [← heφ, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Subalgebra.smul_def,
        smul_eq_mul, mul_one,
      show ((d : A) ⊗ₜ[↥D] (1 : ((𝒱.pullback c ↥D).cover (Limits.pullback.snd c (specMap R
          ↥D))).A01)) =
        algebraMap A _ (d : A) from rfl, AlgEquiv.commutes]
  have hfn : φU01 𝒱 c A D (((Limits.pullback.fst c (specMap R ↥D)).app (𝒱.U0 ⊓ 𝒱.U1)).hom γ) =
      ((Limits.pullback.fst c (specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom γ := by
    have h := Scheme.Hom.appLE_app_apply_of_comp_eq
      (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R ↥D A)))
      (Limits.pullback.fst c (specMap R ↥D)) (Limits.pullback.fst c (specMap R A))
      (baseChangeSnd_fst c (stageHom R (IsScalarTower.toAlgHom R ↥D A))) ((𝒱.U0 ⊓ 𝒱.U1))
          (((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1))
      (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R ↥D A))).ge γ
    rw [Scheme.Hom.app_eq_appLE (Limits.pullback.fst c (specMap R A))]
    exact h
  rw [show d ⊗ₜ[R] γ = d • ((1 : ↥D) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one],
    show (d : A) ⊗ₜ[R] γ = (d : A) • ((1 : A) ⊗ₜ[R] γ) by rw [TensorProduct.smul_tmul',
        smul_eq_mul, mul_one],
    map_smul eD, map_smul eA, heD, heA]
  change φU01 𝒱 c A D (algebraMap ↥D _ d * _) = algebraMap A _ (d : A) * _
  exact ((φU01 𝒱 c A D).map_mul _ _).trans
    (congrArg₂ (fun x y : ((𝒱.pullback c A).cover
      (Limits.pullback.snd c (specMap R A))).A01 => x * y) hsc hfn)

end GeoDict

section Final

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.TwoChartCech
open _root_.AlgebraicGeometry.FGSubalgebra

theorem exists_fg_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec
        (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε (specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε (specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (stageHom R A₀.val)).L ≅ M.L) := by
  classical
  obtain ⟨hP0, hF0, hrkT0, hP1, hF1, hrkT1, -, -, -⟩ :=
    sectionsOf_isInvertible_projective_finite_finrank (𝒱.pullback c A) (Limits.pullback.snd c
        (specMap R A)) M.L M.isInvertible
  have := hP0; have := hF0; have := hP1; have := hF1
  have : Module.Invertible ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L).M0 :=
    Module.Invertible.of_projective_of_forall_finrank_eq_one _ hrkT0
  have : Module.Invertible ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L).M1 :=
    Module.Invertible.of_projective_of_forall_finrank_eq_one _ hrkT1
  obtain ⟨rbc0, rbc1, hrbc0, hrbc1⟩ :=
      exists_sectionsOf_overlap_linearEquiv_baseChange_of_isInvertible
    (𝒱.pullback c A) (Limits.pullback.snd c (specMap R A)) M.L M.isInvertible
  obtain ⟨eU0, eU1, eU01, -, -, heU0, heU1, heU01, -, -⟩ := exists_baseChangeIsos_structureSheaf 𝒱
      c A
  choose eV0 eV1 eV01 _eH0 _eH1 heV0 heV1 heV01 _h4 _h5 using
    fun D : FGSubalgebra R A => exists_baseChangeIsos_structureSheaf 𝒱 c ↥D.1
  choose eφ0 eφ1 eφ01 heφ0 heφ1 heφ01 using
    fun D : FGSubalgebra R A => exists_stage_baseChangeIsos_structureSheaf 𝒱 c ↥D.1 A
  obtain ⟨D, P0, _, _, _, _, P1, _, _, _, _, hrk0, hrk1, σ, hZ⟩ := exists_fg_gluingData R A
      (𝒱.cover c)
    ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A)))
    ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A)) M.L)
    eU0 eU1 eU01 (cover_ρ0_present 𝒱 c A eU0 eU01 heU0 heU01) (cover_ρ1_present 𝒱 c A eU1 eU01
        heU1 heU01)
    rbc0 hrbc0 rbc1 hrbc1
    (fun D => (𝒱.pullback c ↥D.1).cover (Limits.pullback.snd c (specMap R ↥D.1))) eV0 eV1 eV01
    (fun D => cover_ρ0_present 𝒱 c ↥D.1 (eV0 D) (eV01 D) (heV0 D) (heV01 D))
    (fun D => cover_ρ1_present 𝒱 c ↥D.1 (eV1 D) (eV01 D) (heV1 D) (heV01 D))
    (fun D => φU0 𝒱 c A D.1) (fun D => φU1 𝒱 c A D.1) (fun D => φU01 𝒱 c A D.1)
    eφ0 heφ0 eφ1 heφ1 eφ01 heφ01
    (fun D => φU01_ρ0 𝒱 c A D.1) (fun D => φU01_ρ1 𝒱 c A D.1)
    (fun D => φU0_present 𝒱 c A D.1 (eV0 D) (heV0 D) eU0 heU0 (eφ0 D) (heφ0 D))
    (fun D => φU1_present 𝒱 c A D.1 (eV1 D) (heV1 D) eU1 heU1 (eφ1 D) (heφ1 D))
    (fun D => φU01_present 𝒱 c A D.1 (eV01 D) (heV01 D) eU01 heU01 (eφ01 D) (heφ01 D))
  obtain ⟨L, hL, e0, e1, e01, hC0, hC1⟩ := exists_isInvertible_sectionsOf_equiv_of_projective
      (𝒱.pullback c ↥D.1)
    (Limits.pullback.snd c (specMap R ↥D.1)) P0 P1 hrk0 hrk1 σ
  obtain ⟨β'⟩ := hZ ((𝒱.pullback c ↥D.1).sectionsOf (Limits.pullback.snd c (specMap R ↥D.1)) L) e0
      e1 e01 hC0 hC1
  obtain ⟨γ0, γ1, γ01, gr0, gr1, -, -, -, gs0, gs1, gs01⟩ :=
    exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 c ↥D.1 A L hL.1
  let β : ChartBC (k := ↥D.1) (A' := A) (φU0 𝒱 c A D.1) (φU1 𝒱 c A D.1) (φU01 𝒱 c A D.1)
      ((𝒱.pullback c ↥D.1).sectionsOf (Limits.pullback.snd c (specMap R ↥D.1)) L)
      ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (specMap R A))
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R
            ↥D.1 A)))).obj L)) :=
    ⟨γ0, γ1, γ01, gr0, gr1, gs0, gs1, gs01⟩
  obtain ⟨E0, E1, E01, hE0, hE1⟩ := ChartBC.exists_chartIso_of_intertwines β β'
    (mem_span_range_of_algEquiv (eφ0 D) _ (heφ0 D)) (mem_span_range_of_algEquiv (eφ1 D) _ (heφ1 D))
    (mem_span_range_of_algEquiv (eφ01 D) _ (heφ01 D))
    (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (fun _ _ => rfl) (fun _ _
        => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨eL⟩ := nonempty_iso_of_sectionsOf_linearEquiv_of_isInvertible (𝒱.pullback c A)
    (Limits.pullback.snd c (specMap R A)) _ _ (hL.pullback _) M.isInvertible E0 E1 E01 hE0 hE1
  have hval : IsScalarTower.toAlgHom R ↥D.1 A = D.1.val := AlgHom.ext fun _ => rfl
  rw [hval] at eL
  refine ⟨D.1, D.2, RigidifiedLineBundle.ofInvertible L hL, ?_⟩
  obtain ⟨i1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_pullbackAlong_iso (ε := ε) (stageHom R
      D.1.val) hL
  obtain ⟨i2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := ε)
    (hL.pullback (RelPicard.baseChangeSnd c (stageHom R D.1.val))) M.isInvertible eL
  obtain ⟨i3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (ε := ε) M
  exact ⟨i1 ≪≫ i2 ≪≫ i3⟩

end Final

end AlgebraicGeometry.RelPicard.LFP

open LFP_exists_fg_nonempty_iso_pullbackAlong.AlgebraicGeometry.RelPicard in
theorem _root_.AlgebraicGeometry.RelPicard.LFP.exists_fg_nonempty_iso_pullbackAlong
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec
        (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (M : RigidifiedLineBundle c ε
        (Scheme.TwoAffineOpenCover.specMap R A)) :
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (M₀ : RigidifiedLineBundle c ε
        (Scheme.TwoAffineOpenCover.specMap R A₀)),
      Nonempty ((M₀.pullbackAlong (RelPicard.LFP.stageHom R A₀.val)).L ≅ M.L) :=
  LFP.exists_fg_nonempty_iso_pullbackAlong
    R 𝒱 c ε A M
end JacobianVarieties.Picard.Proofs.LFP_exists_fg_nonempty_iso_pullbackAlong
end ProofImplementation

open _root_.AlgebraicGeometry.FGSubalgebra
  (instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
   instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram) in
open _root_.PresheafOfModules.InternalHom
  (instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
   instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
   instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies) in
attribute [-instance]
  AlgebraicGeometry.FGSubalgebra.instIsDirectedLe
  instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite
  AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instNonempty
  AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG
  instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG
  AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram
  AlgebraicGeometry.FGSubalgebra.instIsFiltered
  AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  PresheafOfModules.instMonoidalClosed
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
open _root_.PresheafOfModules.PullbackMonoidal
  (instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb) in
attribute [-instance]
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq
  GoodReductionJacobian.schemeHomOverComp_coe
  NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply
  NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  SheafOfModules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val
attribute [-simp]
  PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
