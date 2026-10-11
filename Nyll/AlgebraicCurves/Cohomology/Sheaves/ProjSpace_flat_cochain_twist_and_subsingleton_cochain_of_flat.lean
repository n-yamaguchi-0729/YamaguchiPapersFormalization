/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_isProper
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_isQuasicoherent_twist
import Nyll.AlgebraicCurves.Geometry.Projective.ProjSpace_isCoherent_twist_and_flat

/-!
# Proj Space flat cochain twist and subsingleton cochain of flat
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat
attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mWs6K4A

section Inter
variable {n : ℕ}

theorem inter_le_pullbackChart {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) (t : Fin (i + 1)) :
    (ProjSpace.stdCoverPullback φ).inter s ≤ ProjSpace.pullbackChart φ ((s.1 t).down) := by
  exact (Scheme.OrderedAffineCover.inter_le _ s t).trans_eq
    (ProjSpace.pullbackChart_eq_stdCoverPullback_U φ ((s.1 t).down)).symm

theorem isAffineOpen_inter {W : Scheme.{u}} {R : Type u} [CommRing R]
    (φ : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsAffineHom φ]
    {i : ℕ} (s : (ProjSpace.stdCoverPullback φ).Idx i) :
    IsAffineOpen ((ProjSpace.stdCoverPullback φ).inter s) := by
  have : (ProjSpace.stdCoverPullback φ).inter s = φ ⁻¹ᵁ (⨅ j, (ProjSpace.stdCover R n).U (s.1 j))
    := by
    change (⨅ j, (ProjSpace.stdCoverPullback φ).U (s.1 j)) = _
    rw [Scheme.OrderedAffineCover.preimage_iInf_fin]
    rfl
  rw [this]
  refine IsAffineOpen.preimage ?_ φ
  have key : ∀ (m : ℕ) (g : Fin (m + 1) → MvPolynomial (Fin (n + 1)) R),
      (⨅ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (g j))
        = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (∏ j, g j) := by
    intro m
    induction m with
    | zero =>
      intro g
      rw [Fin.prod_univ_one]
      exact le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)
    | succ m ih =>
      intro g
      rw [Fin.prod_univ_succ, Proj.basicOpen_mul, ← ih (fun j => g j.succ)]
      exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
        (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  have hdeg : ∀ (m : ℕ) (t : Fin (m + 1) → Fin (n + 1)),
      (∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (m + 1) := by
    intro m t
    have := SetLike.prod_mem_graded (A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (F := (Finset.univ : Finset (Fin (m + 1)))) (i := fun _ => (1 : ℕ)) (g := fun j =>
        MvPolynomial.X (t j))
      (fun j _ => ProjSpace.X_mem_one R n (t j))
    simpa using this
  change IsAffineOpen (⨅ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X ((s.1 j).down)))
  rw [key]
  exact Proj.isAffineOpen_basicOpen _ _ (hdeg i (fun j => (s.1 j).down)) (Nat.succ_pos _)

end Inter

theorem flat_sections {A : Type u} [CommRing A] {Z : Scheme.{u}} (πZ : Z ⟶ Spec (CommRingCat.of A))
  [Flat πZ]
    (U : Z.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom πZ U
    Module.Flat A Γ(Z, U) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.Flat :=
    RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of
      A)).symm.commRingCatIsoToRingEquiv.bijective
  have h2 : (πZ.appLE ⊤ U le_top).hom.Flat :=
    πZ.flat_appLE (isAffineOpen_top _) hU le_top
  exact RingHom.Flat.comp h1 h2

theorem flat_cochain {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    [Flat (ι ≫ ProjSpace.π A n)] (d i : ℕ) :
    Module.Flat A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback
      ι) i) := by
  have : ∀ s : (ProjSpace.stdCoverPullback ι).Idx i,
      Module.Flat A (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback
        ι).inter s)) := by
    intro s
    obtain ⟨f, -, -⟩ := AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
      (ι ≫ ProjSpace.π A n) ι d
      (inter_le_pullbackChart ι s 0)
    let := Scheme.TwoAffineOpenCover.algebraOfHom (ι ≫ ProjSpace.π A n)
      ((ProjSpace.stdCoverPullback ι).inter s)
    have : IsScalarTower A Γ(Z, (ProjSpace.stdCoverPullback ι).inter s)
        (ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s)) :=
      (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).isScalarTower _
    have := flat_sections (ι ≫ ProjSpace.π A n) ((ProjSpace.stdCoverPullback ι).inter s)
      (isAffineOpen_inter ι s)
    exact Module.Flat.of_linearEquiv (f.restrictScalars A)
  change Module.Flat A (∀ s : (ProjSpace.stdCoverPullback ι).Idx i,
    ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter s))
  classical
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype A ((ProjSpace.stdCoverPullback ι).Idx i)
      (fun s => ProjSpace.twistObj (ι ≫ ProjSpace.π A n) ι d ((ProjSpace.stdCoverPullback ι).inter
        s))).symm

theorem subsingleton_cochain {R : Type u} [CommRing R] {n : ℕ} {V : Scheme.{u}} {π : V ⟶ Spec (.of
  R)}
    (F : OModulePresheaf π) (φ : V ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
      [IsAffineHom φ]
    (i : ℕ) (hi : n + 1 ≤ i) : Subsingleton (F.cochain (ProjSpace.stdCoverPullback φ) i) := by
  have : IsEmpty ((ProjSpace.stdCoverPullback φ).Idx i) := ⟨fun s => by
    have := Fintype.card_le_of_injective _ s.2.injective
    have hc : Fintype.card (ProjSpace.stdCoverPullback φ).ι = n + 1 := by
      change Fintype.card (ULift (Fin (n + 1))) = n + 1
      rw [Fintype.card_ulift, Fintype.card_fin]
    rw [Fintype.card_fin, hc] at this
    omega⟩
  infer_instance

end P2mWs6K4A

open P2mWs6K4A in
theorem _root_.AlgebraicGeometry.ProjSpace.flat_cochain_twist_and_subsingleton_cochain_of_flat
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsClosedImmersion ι]
    (hfl : Flat (ι ≫ ProjSpace.π A n)) (d : ℕ) :
    (∀ i : ℕ, Module.Flat A ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain
      (ProjSpace.stdCoverPullback ι) i)) ∧
    (∀ i : ℕ, n + 1 ≤ i →
      Subsingleton ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback
        ι) i)) := by
  have := hfl
  exact ⟨fun i => flat_cochain ι d i, fun i hi => subsingleton_cochain _ ι i hi⟩
end ProjSpace_flat_cochain_twist_and_subsingleton_cochain_of_flat
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
