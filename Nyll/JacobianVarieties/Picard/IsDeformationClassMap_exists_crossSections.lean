/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_exists_crossSections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Models.Places
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Nyll.JacobianVarieties.Picard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
import Nyll.JacobianVarieties.Picard.exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Cross sections comparing deformation class representatives
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationCrossSections
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open  CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover

noncomputable section

namespace CoverCross

section Thick

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (A : Type u) [CommRing
  A] [Algebra R A]

/-- The curve after extension of scalars to the coefficient ring. -/
abbrev XA : Scheme.{u} := Limits.pullback c (specMap R A)

/-- The curve after extension of scalars to the dual number ring. -/
abbrev XD : Scheme.{u} := Limits.pullback c (specMap R (DualNumber A))

/-- The morphism from the dual number thickening to the original base change. -/
abbrev σ : XD c A ⟶ XA c A :=
  RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))

variable {c A}

/-- The homomorphism on sections induced by the thickening projection. -/
abbrev ι {U : (XA c A).Opens} {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U') :
    Γ(XA c A, U) →+* Γ(XD c A, U') :=
  ((σ c A).appLE U U' h.ge).hom

private def _root_.CoverCross.eps (U' : (XD c A).Opens) : Γ(XD c A, U') :=
  let : Algebra (DualNumber A) Γ(XD c A, U') :=
    algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  algebraMap (DualNumber A) Γ(XD c A, U') DualNumber.eps

export _root_.CoverCross (eps)

private theorem _root_.CoverCross.eps_mul_eps (U' : (XD c A).Opens) :
    eps (c := c) (A := A) U' * eps U' = 0 := by
  let : Algebra (DualNumber A) Γ(XD c A, U') :=
    algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  change algebraMap (DualNumber A) Γ(XD c A, U') DualNumber.eps * algebraMap (DualNumber A) _
    DualNumber.eps = 0
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

export _root_.CoverCross (eps_mul_eps)

/-- Restriction preserves the nilpotent parameter on the thickening. -/
theorem map_eps {U' V' : (XD c A).Opens} (hV : V' ≤ U') :
    ((XD c A).presheaf.map (homOfLE hV).op).hom (eps U') = eps V' := by
  let : Algebra (DualNumber A) Γ(XD c A, U') :=
    algebraOfHom (pullback.snd c (specMap R (DualNumber A))) U'
  let : Algebra (DualNumber A) Γ(XD c A, V') :=
    algebraOfHom (pullback.snd c (specMap R (DualNumber A))) V'
  exact (restrictAlgHom (pullback.snd c (specMap R (DualNumber A))) hV).commutes DualNumber.eps

/-- The map from base sections commutes with restriction. -/
theorem map_ι {U V : (XA c A).Opens} {U' V' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    (hV : σ c A ⁻¹ᵁ V = V')
    (hVU : V ≤ U) (hVU' : V' ≤ U') (a : Γ(XA c A, U)) :
    ((XD c A).presheaf.map (homOfLE hVU').op).hom (ι hU a) = ι hV (((XA c A).presheaf.map (homOfLE
      hVU).op).hom a) := by
  change ((σ c A).appLE U U' hU.ge ≫ (XD c A).presheaf.map (homOfLE hVU').op).hom a =
    ((XA c A).presheaf.map (homOfLE hVU).op ≫ (σ c A).appLE V V' hV.ge).hom a
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Multiplication of split sections uses the square zero relation. -/
theorem mul_split {U : (XA c A).Opens} {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (x y x' y' : Γ(XA c A, U)) :
    (ι h x + eps U' * ι h y) * (ι h x' + eps U' * ι h y') =
      ι h (x * x') + eps U' * ι h (x * y' + x' * y) := by
  have he := eps_mul_eps (c := c) (A := A) U'
  simp only [map_mul, map_add]
  linear_combination (ι h y * ι h y') * he

/-- The constant coordinate of a section on the dual number thickening. -/
def cst {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : Γ(XA c A, U) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose.1

/-- The linear coordinate of a section on the dual number thickening. -/
def lin {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens} (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : Γ(XA c A, U) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose.2

/-- The constant and linear coordinates reconstruct a section. -/
theorem split_eq {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens}
    (h : σ c A ⁻¹ᵁ U = U')
    (u : Γ(XD c A, U')) : u = ι h (cst hUa h u) + eps U' * ι h (lin hUa h u) :=
  (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h u).choose_spec.1

/-- The constant and linear coordinates are uniquely determined. -/
theorem split_unique {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens}
    (h : σ c A ⁻¹ᵁ U = U')
    {a b a' b' : Γ(XA c A, U)} (e : ι h a + eps U' * ι h b = ι h a' + eps U' * ι h b') : a = a' ∧ b
      = b' := by
  have H := (existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen c A U hUa U' h
    (ι h a + eps U' * ι h b)).unique (y₁ := (a, b)) (y₂ := (a', b')) rfl e
  exact ⟨congrArg Prod.fst H, congrArg Prod.snd H⟩

end Thick

end CoverCross

namespace CoverCross

section Frames

variable {X : Scheme.{u}} {M : X.Modules}

/-- Successive restrictions of module sections equal their composite. -/
theorem map_map {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h2).op (M.presheaf.map (homOfLE h1).op s) =
      M.presheaf.map (homOfLE (h2.trans h1)).op s := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- Successive restrictions of ring sections equal their composite. -/
theorem map_map_ring {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (r : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom r) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom r := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Restriction along the identity inclusion fixes a module section. -/
theorem map_homOfLE_refl {U : X.Opens} (s : Γ(M, U)) :
    M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, M.presheaf.map_id]
  rfl

/-- An equality relating scalar multiples of sections restricts to smaller opens. -/
theorem restrict_smul_eq {U U' W T : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U') (hTW : T ≤ W)
    {s : Γ(M, U)} {t : Γ(M, U')} {u : Γ(X, W)}
    (h : u • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU').op t) :
    (X.presheaf.map (homOfLE hTW).op).hom u • M.presheaf.map (homOfLE (hTW.trans hWU)).op s =
      M.presheaf.map (homOfLE (hTW.trans hWU')).op t := by
  have := congrArg (M.presheaf.map (homOfLE hTW).op) h
  rw [Scheme.Modules.map_smul, map_map, map_map] at this
  exact this

/-- Two frames on an overlap differ by a unit. -/
theorem exists_units_of_isFrameOn {U U' W : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U')
    {s : Γ(M, U)} {s' : Γ(M, U')} (hs : Scheme.Modules.IsFrameOn s U) (hs' :
      Scheme.Modules.IsFrameOn s' U') :
    ∃ v w : Γ(X, W), v • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU').op s' ∧
      w • M.presheaf.map (homOfLE hWU').op s' = M.presheaf.map (homOfLE hWU).op s ∧ v * w = 1 := by
  obtain ⟨v, hv⟩ := (hs hWU hWU).2 (M.presheaf.map (homOfLE hWU').op s')
  obtain ⟨w, hw⟩ := (hs' hWU' hWU').2 (M.presheaf.map (homOfLE hWU).op s)
  beta_reduce at hv hw
  refine ⟨v, w, hv, hw, ?_⟩
  apply (hs hWU hWU).1
  change (v * w) • M.presheaf.map (homOfLE hWU).op s = (1 : Γ(X, W)) • M.presheaf.map (homOfLE
    hWU).op s
  rw [one_smul, mul_comm, mul_smul, hv, hw]

/-- Transition units satisfy the compatibility identity across the first cover. -/
theorem cross_identity {P0 P1 Q : X.Opens} {e0 : Γ(M, P0)} {e1 : Γ(M, P1)} {e' : Γ(M, Q)}
    (hF0 : Scheme.Modules.IsFrameOn e0 P0) (g : Γ(X, P0 ⊓ P1))
    (hg : M.presheaf.map (homOfLE inf_le_right).op e1 = g • M.presheaf.map (homOfLE inf_le_left).op
      e0)
    (u0 : Γ(X, P0 ⊓ Q))
    (hu0 : u0 • M.presheaf.map (homOfLE inf_le_left).op e0 = M.presheaf.map (homOfLE
      inf_le_right).op e')
    (u1 : Γ(X, P1 ⊓ Q))
    (hu1 : u1 • M.presheaf.map (homOfLE inf_le_left).op e1 = M.presheaf.map (homOfLE
      inf_le_right).op e') :
    (X.presheaf.map (homOfLE (inf_le_inf_right Q inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ Q)).op).hom u0 =
      (X.presheaf.map (homOfLE (inf_le_inf_right Q inf_le_right : (P0 ⊓ P1) ⊓ Q ≤ P1 ⊓ Q)).op).hom
        u1 *
      (X.presheaf.map (homOfLE (inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ P1)).op).hom g := by
  have h0 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_right Q inf_le_left : (P0 ⊓ P1)
    ⊓ Q ≤ P0 ⊓ Q) hu0
  have h1 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_right Q inf_le_right : (P0 ⊓ P1)
    ⊓ Q ≤ P1 ⊓ Q) hu1
  have h2 := congrArg (M.presheaf.map (homOfLE (inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0 ⊓ P1)).op) hg
  rw [Scheme.Modules.map_smul, map_map, map_map] at h2
  apply (hF0 (inf_le_left.trans inf_le_left : (P0 ⊓ P1) ⊓ Q ≤ P0) (inf_le_left.trans inf_le_left)).1
  change _ • _ = (_ * _) • _
  rw [mul_smul]
  erw [h0, ← h2]
  exact h1.symm

/-- Transition units satisfy the compatibility identity across the second cover. -/
theorem cross_identity' {P Q0 Q1 : X.Opens} {e : Γ(M, P)} {e0' : Γ(M, Q0)} {e1' : Γ(M, Q1)}
    (hF : Scheme.Modules.IsFrameOn e P) (g' : Γ(X, Q0 ⊓ Q1))
    (hg' : M.presheaf.map (homOfLE inf_le_right).op e1' = g' • M.presheaf.map (homOfLE
      inf_le_left).op e0')
    (u0 : Γ(X, P ⊓ Q0))
    (hu0 : u0 • M.presheaf.map (homOfLE inf_le_left).op e = M.presheaf.map (homOfLE
      inf_le_right).op e0')
    (u1 : Γ(X, P ⊓ Q1))
    (hu1 : u1 • M.presheaf.map (homOfLE inf_le_left).op e = M.presheaf.map (homOfLE
      inf_le_right).op e1') :
    (X.presheaf.map (homOfLE (inf_le_inf_left P inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q1)).op).hom u1 =
      (X.presheaf.map (homOfLE (inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ Q0 ⊓ Q1)).op).hom g' *
      (X.presheaf.map (homOfLE (inf_le_inf_left P inf_le_left : P ⊓ (Q0 ⊓ Q1) ≤ P ⊓ Q0)).op).hom u0
        := by
  have h0 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_left P inf_le_left : P ⊓ (Q0 ⊓
    Q1) ≤ P ⊓ Q0) hu0
  have h1 := restrict_smul_eq inf_le_left inf_le_right (inf_le_inf_left P inf_le_right : P ⊓ (Q0 ⊓
    Q1) ≤ P ⊓ Q1) hu1
  have h2 := congrArg (M.presheaf.map (homOfLE (inf_le_right : P ⊓ (Q0 ⊓ Q1) ≤ Q0 ⊓ Q1)).op) hg'
  rw [Scheme.Modules.map_smul, map_map, map_map] at h2
  apply (hF (inf_le_left : P ⊓ (Q0 ⊓ Q1) ≤ P) inf_le_left).1
  change _ • _ = (_ * _) • _
  rw [mul_smul]
  erw [h1, h0, ← h2]

end Frames

end CoverCross

namespace CoverCross

section Transport

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u} [CommRing
  A] [Algebra R A]

/-- The thickening projection preserves the specified intersections of opens. -/
theorem pre_inf {U V : (XA c A).Opens} {U' V' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    (hV : σ c A ⁻¹ᵁ V = V') :
    σ c A ⁻¹ᵁ (U ⊓ V) = U' ⊓ V' := by
  rw [Scheme.Hom.preimage_inf, hU, hV]

/-- Restriction preserves a split constant plus nilpotent expression. -/
theorem map_split_expr {U T : (XA c A).Opens} {U' T' : (XD c A).Opens} (hU : σ c A ⁻¹ᵁ U = U')
    (hT : σ c A ⁻¹ᵁ T = T') (hTU : T ≤ U) (hTU' : T' ≤ U') (a b : Γ(XA c A, U)) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom (ι hU a + eps U' * ι hU b) =
      ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom a) + eps T' * ι hT (((XA c A).presheaf.map
        (homOfLE hTU).op).hom b) := by
  rw [map_add, map_mul, map_ι hU hT hTU hTU', map_ι hU hT hTU hTU', map_eps]

/-- Both coordinates of a split section commute with restriction. -/
theorem map_split {U T : (XA c A).Opens} (hUa : IsAffineOpen U) {U' T' : (XD c A).Opens}
    (hU : σ c A ⁻¹ᵁ U = U')
    (hT : σ c A ⁻¹ᵁ T = T') (hTU : T ≤ U) (hTU' : T' ≤ U') (u : Γ(XD c A, U')) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom u =
      ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom (cst hUa hU u)) +
        eps T' * ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom (lin hUa hU u)) := by
  conv_lhs => rw [split_eq hUa hU u]
  exact map_split_expr hU hT hTU hTU' _ _

/-- The constant coordinate of a product is the product of constant coordinates. -/
theorem cst_mul_cst {U : (XA c A).Opens} (hUa : IsAffineOpen U) {U' : (XD c A).Opens}
    (hU : σ c A ⁻¹ᵁ U = U')
    {u w : Γ(XD c A, U')} (huw : u * w = 1) : cst hUa hU u * cst hUa hU w = 1 := by
  have h := huw
  rw [split_eq hUa hU u, split_eq hUa hU w, mul_split] at h
  have h1 : (1 : Γ(XD c A, U')) = ι hU 1 + eps U' * ι hU 0 :=
    by rw [map_one, map_zero, mul_zero, add_zero]
  rw [h1] at h
  exact (split_unique hUa hU h).1

end Transport

end CoverCross

namespace CoverCross

section Main

/-- A transition equality determines both coordinates of the first factor. -/
theorem coords_of_eq {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u}
    [CommRing A]
    [Algebra R A] {T : (XA c A).Opens} (hTa : IsAffineOpen T) {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ
      T = T')
    {a0 b0 a1 b1 f : Γ(XA c A, T)}
    (h : ι hT a0 + eps T' * ι hT b0 = (ι hT a1 + eps T' * ι hT b1) * (1 + eps T' * ι hT f)) :
    a0 = a1 ∧ b0 = a1 * f + b1 := by
  have h1 : (1 : Γ(XD c A, T')) + eps T' * ι hT f = ι hT 1 + eps T' * ι hT f := by rw [map_one]
  rw [h1, mul_split, mul_one, one_mul] at h
  exact split_unique hTa hT h

/-- A transition equality determines both coordinates of the second factor. -/
theorem coords_of_eq' {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {A : Type u}
    [CommRing A]
    [Algebra R A] {T : (XA c A).Opens} (hTa : IsAffineOpen T) {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ
      T = T')
    {a0 b0 a1 b1 f : Γ(XA c A, T)}
    (h : ι hT a1 + eps T' * ι hT b1 = (1 + eps T' * ι hT f) * (ι hT a0 + eps T' * ι hT b0)) :
    a1 = a0 ∧ b1 = a0 * f + b0 := by
  have h1 : (1 : Γ(XD c A, T')) + eps T' * ι hT f = ι hT 1 + eps T' * ι hT f := by rw [map_one]
  rw [h1, mul_split, one_mul, one_mul] at h
  obtain ⟨H1, H2⟩ := split_unique hTa hT h
  exact ⟨H1, by rw [H2]; ring⟩

/-- Restricting an infinitesimal unit restricts its coefficient. -/
theorem map_oneAddEpsMul {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {A : Type u} [CommRing A]
    [Algebra R A] (𝒲 : C.TwoAffineOpenCover)
    (hW01 : σ c A ⁻¹ᵁ ((𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1) =
      (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
    {T : (XA c A).Opens} {T' : (XD c A).Opens} (hT : σ c A ⁻¹ᵁ T = T')
    (hTU : T ≤ (𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1)
    (hTU' : T' ≤ (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
    (f : Γ(XA c A, (𝒲.pullback c A).U0 ⊓ (𝒲.pullback c A).U1)) :
    ((XD c A).presheaf.map (homOfLE hTU').op).hom
        (show Γ(XD c A, (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒲 c f) =
      1 + eps T' * ι hT (((XA c A).presheaf.map (homOfLE hTU).op).hom f) := by
  have e : (show Γ(XD c A, (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1)
      from oneAddEpsMul A 𝒲 c f) = 1 + eps _ * ι hW01 f := rfl
  rw [e, map_add, map_one, map_mul, map_eps, map_ι hW01 hT hTU hTU']
private theorem restrict_coboundary_eq {X : Scheme.{u}} {U₀ U₁ T : X.Opens}
    (hT : T ≤ U₀ ⊓ U₁) (p₀ : Γ(X, U₀)) (p₁ : Γ(X, U₁))
    (f s : Γ(X, U₀ ⊓ U₁))
    (h : (X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom p₁ -
      (X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom p₀ + f = s) :
    (X.presheaf.map (homOfLE (hT.trans inf_le_right)).op).hom p₁ -
      (X.presheaf.map (homOfLE (hT.trans inf_le_left)).op).hom p₀ +
      (X.presheaf.map (homOfLE hT).op).hom f =
        (X.presheaf.map (homOfLE hT).op).hom s := by
  have hmap := congrArg (fun z : Γ(X, U₀ ⊓ U₁) =>
    (X.presheaf.map (homOfLE hT).op).hom z) h
  rw [map_add (X.presheaf.map (homOfLE hT).op).hom,
    map_sub (X.presheaf.map (homOfLE hT).op).hom,
    map_map_ring (X := X) (inf_le_right : U₀ ⊓ U₁ ≤ U₁) hT p₁,
    map_map_ring (X := X) (inf_le_left : U₀ ⊓ U₁ ≤ U₀) hT p₀] at hmap
  exact hmap

/-- Construct cross sections between two representatives of a deformation class. -/
theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲}
    {δ' : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲'}
    (hδ : IsDeformationClassMap c ε A 𝒲 δ) (hδ' : IsDeformationClassMap c ε A 𝒲' δ')
    (x : RigKerDualNumber c ε A)
    (s : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (s' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0
    let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0
    let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓
        V0)).op).hom g00
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓
          V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom s ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓
          V1)).op).hom g11
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom s ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
          V0)).op).hom g00
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
        V1)).op).hom g11
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
          V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s'
            := by
  intro X' W0 W1 V0 V1
  simp only [X']
  obtain ⟨M, rfl⟩ := Quotient.exists_rep x
  obtain ⟨e0, e1, f, hF0, hF1, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒲 M
  obtain ⟨e0', e1', f', hF0', hF1', hM'⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒲' M
  have hc : (Submodule.Quotient.mk s : H1StructureSheaf c A 𝒲) = Submodule.Quotient.mk f :=
    hs.symm.trans (hδ M e0 e1 f hF0 hF1 hM)
  have hc' : (Submodule.Quotient.mk s' : H1StructureSheaf c A 𝒲') = Submodule.Quotient.mk f' :=
    hs'.symm.trans (hδ' M e0' e1' f' hF0' hF1' hM')
  obtain ⟨p, hp⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hc)
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1 ((Submodule.Quotient.eq _).1 hc')
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r0_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, Units.val_one, one_mul] at hp hq
  change ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ W1 ≤ W1)).op).hom p.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op).hom p.1 =
      (s : Γ(XA c A, W0 ⊓ W1)) - (f : Γ(XA c A, W0 ⊓ W1)) at hp
  have hp2 : ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ W1 ≤ W1)).op).hom p.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op).hom p.1 + (show Γ(XA c A,
        W0 ⊓ W1) from f) =
      (show Γ(XA c A, W0 ⊓ W1) from s) := by
    rw [hp]; exact sub_add_cancel s f
  change ((XA c A).presheaf.map (homOfLE (inf_le_right : V0 ⊓ V1 ≤ V1)).op).hom q.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : V0 ⊓ V1 ≤ V0)).op).hom q.1 =
      (s' : Γ(XA c A, V0 ⊓ V1)) - (f' : Γ(XA c A, V0 ⊓ V1)) at hq
  have hq2 : ((XA c A).presheaf.map (homOfLE (inf_le_right : V0 ⊓ V1 ≤ V1)).op).hom q.2 -
      ((XA c A).presheaf.map (homOfLE (inf_le_left : V0 ⊓ V1 ≤ V0)).op).hom q.1 + (show Γ(XA c A,
        V0 ⊓ V1) from f') =
      (show Γ(XA c A, V0 ⊓ V1) from s') := by
    rw [hq]; exact sub_add_cancel s' f'
  obtain ⟨z00, z01, z10, z11, H0, H1, H0', H1'⟩ :=
    AlgebraicGeometry.RelPicard.exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
      c A 𝒲 𝒲' M.1.L e0 e1 f hF0 hF1 hM e0' e1' f' hF0' hF1' hM'
  have HP0 := restrict_coboundary_eq (X := XA c A)
    (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1) p.1 p.2 f s hp2
  have HP1 := restrict_coboundary_eq (X := XA c A)
    (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1) p.1 p.2 f s hp2
  have HQ0 := restrict_coboundary_eq (X := XA c A)
    (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1) q.1 q.2 f' s' hq2
  have HQ1 := restrict_coboundary_eq (X := XA c A)
    (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1) q.1 q.2 f' s' hq2
  refine ⟨z00 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ V0 ≤ W0)).op).hom p.1
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ V0 ≤ V0)).op).hom q.1,
          z01 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W0 ⊓ V1 ≤ W0)).op).hom p.1
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ V1 ≤ V1)).op).hom q.2,
          z10 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W1 ⊓ V0 ≤ W1)).op).hom p.2
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ V0 ≤ V0)).op).hom q.1,
          z11 - ((XA c A).presheaf.map (homOfLE (inf_le_left : W1 ⊓ V1 ≤ W1)).op).hom p.2
            + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ V1 ≤ V1)).op).hom q.2, ?_, ?_,
              ?_, ?_⟩
  · simp only [map_sub, map_add]
    rw [map_map_ring (X := XA c A)
        (inf_le_left : W0 ⊓ V0 ≤ W0)
        (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0) p.1,
      map_map_ring (X := XA c A)
        (inf_le_right : W0 ⊓ V0 ≤ V0)
        (inf_le_inf_right V0 inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ V0) q.1,
      map_map_ring (X := XA c A)
        (inf_le_left : W1 ⊓ V0 ≤ W1)
        (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0) p.2,
      map_map_ring (X := XA c A)
        (inf_le_right : W1 ⊓ V0 ≤ V0)
        (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓ V0) q.1]
    linear_combination H0 + HP0
  · simp only [map_sub, map_add]
    rw [map_map_ring (X := XA c A)
        (inf_le_left : W0 ⊓ V1 ≤ W0)
        (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1) p.1,
      map_map_ring (X := XA c A)
        (inf_le_right : W0 ⊓ V1 ≤ V1)
        (inf_le_inf_right V1 inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ V1) q.2,
      map_map_ring (X := XA c A)
        (inf_le_left : W1 ⊓ V1 ≤ W1)
        (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1) p.2,
      map_map_ring (X := XA c A)
        (inf_le_right : W1 ⊓ V1 ≤ V1)
        (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓ V1) q.2]
    linear_combination H1 + HP1
  · simp only [map_sub, map_add]
    rw [map_map_ring (X := XA c A)
        (inf_le_left : W0 ⊓ V1 ≤ W0)
        (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1) p.1,
      map_map_ring (X := XA c A)
        (inf_le_right : W0 ⊓ V1 ≤ V1)
        (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V1) q.2,
      map_map_ring (X := XA c A)
        (inf_le_left : W0 ⊓ V0 ≤ W0)
        (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0) p.1,
      map_map_ring (X := XA c A)
        (inf_le_right : W0 ⊓ V0 ≤ V0)
        (inf_le_inf_left W0 inf_le_left : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓ V0) q.1]
    linear_combination H0' + HQ0
  · simp only [map_sub, map_add]
    rw [map_map_ring (X := XA c A)
        (inf_le_left : W1 ⊓ V1 ≤ W1)
        (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1) p.2,
      map_map_ring (X := XA c A)
        (inf_le_right : W1 ⊓ V1 ≤ V1)
        (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V1) q.2,
      map_map_ring (X := XA c A)
        (inf_le_left : W1 ⊓ V0 ≤ W1)
        (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0) p.2,
      map_map_ring (X := XA c A)
        (inf_le_right : W1 ⊓ V0 ≤ V0)
        (inf_le_inf_left W1 inf_le_left : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓ V0) q.1]
    linear_combination H1' + HQ1

end Main

end CoverCross

end

end JacobianVarieties.Picard.Proofs.DeformationCrossSections

namespace AlgebraicGeometry.RelPicard.IsDeformationClassMap

open _root_.JacobianVarieties.Picard.Proofs.DeformationCrossSections
universe u
open  _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.NeronModelInfra _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.JacobianVarieties.Picard.Proofs.DeformationCrossSections.CoverCross in
/-- Representatives of a deformation class on two covers admit cross sections. -/
theorem exists_crossSections
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲}
    {δ' : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒲'}
    (hδ : IsDeformationClassMap c ε A 𝒲 δ) (hδ' : IsDeformationClassMap c ε A 𝒲' δ')
    (x : RigKerDualNumber c ε A)
    (s : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (s' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hs : δ x = Submodule.Quotient.mk s) (hs' : δ' x = Submodule.Quotient.mk s') :
    let X' := Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)
    let W0 := (𝒲.pullback c A).U0
    let W1 := (𝒲.pullback c A).U1
    let V0 := (𝒲'.pullback c A).U0
    let V1 := (𝒲'.pullback c A).U1
    ∃ (g00 : Γ(X', W0 ⊓ V0)) (g01 : Γ(X', W0 ⊓ V1)) (g10 : Γ(X', W1 ⊓ V0)) (g11 : Γ(X', W1 ⊓ V1)),
      (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_left  : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓
        V0)).op).hom g00
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V0 inf_le_right : (W0 ⊓ W1) ⊓ V0 ≤ W1 ⊓
          V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓
        V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓
          V1)).op).hom g11
          + (X'.presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom s ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
        V1)).op).hom g01
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
          V0)).op).hom g00
          + (X'.presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' ∧
      (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
        V1)).op).hom g11
        = (X'.presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
          V0)).op).hom g10
          + (X'.presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom s' :=
  CoverCross.main c ε A 𝒲 𝒲' hδ hδ' x s s' hs hs'
end AlgebraicGeometry.RelPicard.IsDeformationClassMap
end ProofImplementation
