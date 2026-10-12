/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Projective_exists_baseChange_quotient_iso_of_squareZero
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Projective_exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_TwoAffineOpenCover_exists_isInvertible_sectionsOf_equiv_of_projective
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

/-!
Lift rigidified line bundles across a square-zero extension using a two-affine open cover.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
    NeronModelInfra TensorProduct

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem
_root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.exists_of_squareZero_of_twoAffineOpenCover
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))) :
    ∃ M' : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R B))),
      Nonempty ((M'.pullbackAlong ι).L ≅ M.L) := by
  classical
  have hPL := @Module.Projective.exists_baseChange_quotient_iso_of_squareZero
  have hPIL := @Module.Projective.exists_linearEquiv_of_baseChange_quotient_of_squareZero_of_compat
  have hGI := @Scheme.TwoAffineOpenCover.exists_isInvertible_sectionsOf_equiv_of_projective
  have hCQ :=
    @Scheme.TwoAffineOpenCover.exists_ideal_pullback_cover_ringEquiv_quotient_appLE_of_squareZero
  have hSF := @Scheme.TwoAffineOpenCover.sectionsOf_isInvertible_projective_finite_finrank
  have hN4 :=
    @Scheme.TwoAffineOpenCover.exists_linearEquiv_overlap_quotient_baseChange_of_lift_of_compat
  have hN5 :=
    @nonempty_iso_pullback_baseChangeSnd_of_sectionsOf_lift_appLE_of_overlap_iso
  have hN6 :=
    @RigidifiedLineBundle.nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
  have hN7 := @Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
  let 𝒱B := 𝒱.pullback c B
  let cB := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R B)
  let 𝒱BI := 𝒱.pullback c (B ⧸ I)
  let cBI := pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (B ⧸ I))
  obtain ⟨J0, J1, J01, hJ0, hJ1, hJ01, φ0, φ1, φ01, hφρ0, hφρ1, hψ0, hψ1, hψ01⟩ := hCQ 𝒱 c I hI
  obtain ⟨hproj0, hfin0, hrk0, hproj1, hfin1, hrk1, hproj01, hfin01, hrk01⟩ :=
    hSF 𝒱BI cBI M.L M.isInvertible
  have := hproj0; have := hfin0; have := hproj1; have := hfin1
  have := hproj01; have := hfin01
  set A0B := (𝒱B.cover cB).A0
  set A1B := (𝒱B.cover cB).A1
  set A01B := (𝒱B.cover cB).A01
  set P0 := (𝒱BI.sectionsOf cBI M.L).M0
  set P1 := (𝒱BI.sectionsOf cBI M.L).M1
  let : Module (A0B ⧸ J0) P0 := Module.compHom P0 φ0.toRingHom
  let : Module (A1B ⧸ J1) P1 := Module.compHom P1 φ1.toRingHom
  have : RingHomInvPair (RingEquiv.toRingHom φ0.symm) (RingEquiv.toRingHom φ0) :=
    ⟨RingHom.ext φ0.apply_symm_apply, RingHom.ext φ0.symm_apply_apply⟩
  have : RingHomInvPair (RingEquiv.toRingHom φ0) (RingEquiv.toRingHom φ0.symm) :=
    ⟨RingHom.ext φ0.symm_apply_apply, RingHom.ext φ0.apply_symm_apply⟩
  have : RingHomInvPair (RingEquiv.toRingHom φ1.symm) (RingEquiv.toRingHom φ1) :=
    ⟨RingHom.ext φ1.apply_symm_apply, RingHom.ext φ1.symm_apply_apply⟩
  have : RingHomInvPair (RingEquiv.toRingHom φ1) (RingEquiv.toRingHom φ1.symm) :=
    ⟨RingHom.ext φ1.symm_apply_apply, RingHom.ext φ1.apply_symm_apply⟩
  have : Module.Projective (A0B ⧸ J0) P0 := Module.Projective.of_equiv
    ({ __ := AddEquiv.refl P0
       map_smul' := fun r p => by
         change r • p = φ0 (φ0.symm r) • p; rw [φ0.apply_symm_apply] } :
     P0 ≃ₛₗ[RingEquiv.toRingHom φ0.symm] P0)
  have : Module.Projective (A1B ⧸ J1) P1 := Module.Projective.of_equiv
    ({ __ := AddEquiv.refl P1
       map_smul' := fun r p => by
         change r • p = φ1 (φ1.symm r) • p; rw [φ1.apply_symm_apply] } :
     P1 ≃ₛₗ[RingEquiv.toRingHom φ1.symm] P1)
  have : Module.Finite (A0B ⧸ J0) P0 := by
    obtain ⟨S, hS⟩ := hfin0.1
    exact ⟨⟨S, Submodule.eq_top_iff'.mpr fun p => by
      have hp : p ∈ Submodule.span (𝒱BI.cover cBI).A0 (S : Set P0) := hS ▸ Submodule.mem_top
      induction hp using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (r • x : P0) = (φ0.symm r : A0B ⧸ J0) • x := by
          change r • x = φ0 (φ0.symm r) • x; rw [φ0.apply_symm_apply]
        exact this ▸ Submodule.smul_mem _ _ hx⟩⟩
  have : Module.Finite (A1B ⧸ J1) P1 := by
    obtain ⟨S, hS⟩ := hfin1.1
    exact ⟨⟨S, Submodule.eq_top_iff'.mpr fun p => by
      have hp : p ∈ Submodule.span (𝒱BI.cover cBI).A1 (S : Set P1) := hS ▸ Submodule.mem_top
      induction hp using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span hx
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (r • x : P1) = (φ1.symm r : A1B ⧸ J1) • x := by
          change r • x = φ1 (φ1.symm r) • x; rw [φ1.apply_symm_apply]
        exact this ▸ Submodule.smul_mem _ _ hx⟩⟩
  obtain ⟨P0', _, _, hproj0', hfin0', ⟨iso0⟩⟩ := hPL (R := A0B) J0 hJ0 P0
  obtain ⟨P1', _, _, hproj1', hfin1', ⟨iso1⟩⟩ := hPL (R := A1B) J1 hJ1 P1
  have := hproj0'; have := hfin0'; have := hproj1'; have := hfin1'
  let : Algebra A0B A01B := (𝒱B.cover cB).ρ0.toRingHom.toAlgebra
  let : Algebra A1B A01B := (𝒱B.cover cB).ρ1.toRingHom.toAlgebra
  have : Module.Projective A01B (A01B ⊗[A0B] P0') := by
    infer_instance
  have : Module.Finite A01B (A01B ⊗[A0B] P0') := by
    infer_instance
  have : Module.Projective A01B (A01B ⊗[A1B] P1') := by
    infer_instance
  have : Module.Finite A01B (A01B ⊗[A1B] P1') := by
    infer_instance
  let : Module (A01B ⧸ J01) (𝒱BI.sectionsOf cBI M.L).M01 := Module.compHom _ φ01.toRingHom
  obtain ⟨iso01₀, iso01₁, hiso01₀_r0, hiso01₁_r1⟩ :=
    hN4 c 𝒱 I M.L M.isInvertible J0 J1 J01 φ0 φ1 φ01 hφρ0 hφρ1 P0' P1' iso0 iso1
  let eN4 : (A01B⧸J01) ⊗[A01B] (A01B ⊗[A0B] P0') ≃ₗ[A01B⧸J01] (A01B⧸J01) ⊗[A01B] (A01B ⊗[A1B]
    P1') :=
    iso01₀.trans iso01₁.symm
  obtain ⟨σ', hσ'compat⟩ := hPIL (R := A01B) J01 hJ01 (A01B ⊗[A0B] P0') (A01B ⊗[A1B] P1') eN4
  have hσ'symm : ∀ (y : A01B ⊗[A1B] P1'),
      (1:A01B⧸J01) ⊗ₜ[A01B] σ'.symm y = eN4.symm ((1:A01B⧸J01) ⊗ₜ[A01B] y) := fun y => by
    refine eN4.injective ?_
    rw [LinearEquiv.apply_symm_apply, ← hσ'compat, LinearEquiv.apply_symm_apply]
  have hiso01_r1 : ∀ (p : P1'),
      iso01₀ ((1:A01B⧸J01) ⊗ₜ[A01B] (σ'.symm ((1:A01B) ⊗ₜ[A1B] p))) =
      (𝒱BI.sectionsOf cBI M.L).r1 (iso1 ((1:A1B⧸J1) ⊗ₜ[A1B] p)) := fun p => by
    rw [hσ'symm, show eN4.symm = iso01₁.trans iso01₀.symm from rfl, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, hiso01₁_r1]
  have hrk0' : ∀ (K : Type u) [Field K] [Algebra A0B K],
      Module.finrank K (K ⊗[A0B] P0') = 1 :=
    hN7 J0 hJ0 φ0 P0 P0' hrk0 iso0
  have hrk1' : ∀ (K : Type u) [Field K] [Algebra A1B K],
      Module.finrank K (K ⊗[A1B] P1') = 1 :=
    hN7 J1 hJ1 φ1 P1 P1' hrk1 iso1
  obtain ⟨L', hL'inv, e0', e1', e01', he0', he1'⟩ :=
    hGI 𝒱B cB P0' P1' hrk0' hrk1' σ'
  have hPullInv : Scheme.Modules.IsInvertible
    ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L') := by
    exact hL'inv.pullback (baseChangeSnd c ι)
  obtain ⟨isoL⟩ : Nonempty
    (((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L') ≅ M.L) :=
    hN5 c 𝒱 I ι hι M.L M.isInvertible J0 J1 J01 φ0 φ1 φ01 hφρ0 hφρ1 hψ0 hψ1 hψ01
      P0' P1' iso0 iso1 σ' iso01₀ hiso01₀_r0 hiso01_r1 L' hL'inv e0' e1' e01' he0' he1'
  obtain ⟨rig⟩ : Nonempty
    ((Scheme.Modules.pullback (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      ε)).obj L'
      ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) :=
    hN6 c ε I hI ι hι M L' hL'inv ⟨isoL⟩
  let M' : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    ⟨L', hL'inv, ⟨rig⟩⟩
  refine ⟨M', ⟨?_⟩⟩
  exact isoL
end JacobianVarieties.Picard.Proofs.RigidifiedLineBundle_exists_of_squareZero_of_twoAffineOpenCover
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.RelPicard.LFP.stageHom_val
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
