/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Opposites
import Mathlib.Order.Lattice
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.Basic
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.JacobianVarieties.Picard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen

/-!
# Cross sections for frames on dual number thickenings
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FrameCrossSections
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

private theorem coefficient_transition {S : Type*} [CommRing S]
    {a₀ a₁ b₀ b₁ r₀ r₁ f : S}
    (h₀ : a₀ * r₀ = 1) (h₁ : a₁ * r₁ = 1)
    (hconst : a₀ = a₁) (hlinear : b₀ = a₁ * f + b₁) :
    b₀ * r₀ = b₁ * r₁ + f := by
  have hinv : r₀ = r₁ := by
    linear_combination (-r₀) * h₁ + r₁ * h₀ - (r₀ * r₁) * hconst
  linear_combination r₀ * hlinear + (b₁ + f * a₁) * hinv + f * h₁

private theorem coefficient_transition_restrict
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {A : Type u} [CommRing A] [Algebra R A]
    {U₀ U₁ T : (XA c A).Opens}
    (hU₀a : IsAffineOpen U₀) (hU₁a : IsAffineOpen U₁) (hTa : IsAffineOpen T)
    {U₀' U₁' T' : (XD c A).Opens}
    (hU₀ : σ c A ⁻¹ᵁ U₀ = U₀') (hU₁ : σ c A ⁻¹ᵁ U₁ = U₁')
    (hT : σ c A ⁻¹ᵁ T = T')
    (hT₀ : T ≤ U₀) (hT₁ : T ≤ U₁) (hT₀' : T' ≤ U₀') (hT₁' : T' ≤ U₁')
    {u₀ w₀ : Γ(XD c A, U₀')} {u₁ w₁ : Γ(XD c A, U₁')}
    (huw₀ : u₀ * w₀ = 1) (huw₁ : u₁ * w₁ = 1) (f : Γ(XA c A, T))
    (htransition : ((XD c A).presheaf.map (homOfLE hT₀').op).hom u₀ =
      ((XD c A).presheaf.map (homOfLE hT₁').op).hom u₁ *
        (1 + eps T' * ι hT f)) :
    ((XA c A).presheaf.map (homOfLE hT₀).op).hom
        (lin hU₀a hU₀ u₀ * cst hU₀a hU₀ w₀) =
      ((XA c A).presheaf.map (homOfLE hT₁).op).hom
        (lin hU₁a hU₁ u₁ * cst hU₁a hU₁ w₁) + f := by
  rw [map_split hU₀a hU₀ hT hT₀ hT₀' u₀,
    map_split hU₁a hU₁ hT hT₁ hT₁' u₁] at htransition
  obtain ⟨hconst, hlinear⟩ := coords_of_eq hTa hT htransition
  have hinv₀ := congrArg
    (fun z : Γ(XA c A, U₀) => ((XA c A).presheaf.map (homOfLE hT₀).op).hom z)
    (cst_mul_cst hU₀a hU₀ huw₀)
  have hinv₁ := congrArg
    (fun z : Γ(XA c A, U₁) => ((XA c A).presheaf.map (homOfLE hT₁).op).hom z)
    (cst_mul_cst hU₁a hU₁ huw₁)
  simp only [map_mul, map_one] at hinv₀ hinv₁
  rw [map_mul, map_mul]
  exact coefficient_transition hinv₀ hinv₁ hconst hlinear

/-- Construct cross sections comparing the two chosen systems of local frames. -/
theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (e0 : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e1 : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
    (f : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hF0 : Scheme.Modules.IsFrameOn e0 (𝒲.pullback c (DualNumber A)).U0)
    (hF1 : Scheme.Modules.IsFrameOn e1 (𝒲.pullback c (DualNumber A)).U1)
    (hM : N.presheaf.map (homOfLE inf_le_right).op e1 =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A
            𝒲 c f) •
        N.presheaf.map (homOfLE inf_le_left).op e0)
    (e0' : Γ(N, (𝒲'.pullback c (DualNumber A)).U0)) (e1' : Γ(N, (𝒲'.pullback c (DualNumber A)).U1))
    (f' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (hF0' : Scheme.Modules.IsFrameOn e0' (𝒲'.pullback c (DualNumber A)).U0)
    (hF1' : Scheme.Modules.IsFrameOn e1' (𝒲'.pullback c (DualNumber A)).U1)
    (hM' : N.presheaf.map (homOfLE inf_le_right).op e1' =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) from oneAddEpsMul
            A 𝒲' c f') •
        N.presheaf.map (homOfLE inf_le_left).op e0') :
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
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom f ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓
          V1)).op).hom g11
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom f ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
          V0)).op).hom g00
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f' ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
        V1)).op).hom g11
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
          V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f'
            := by
  intro X' W0 W1 V0 V1
  simp only [X']
  have pW0 : σ c A ⁻¹ᵁ W0 = (𝒲.pullback c (DualNumber A)).U0 := baseChangeSnd_preimage_U0 𝒲 c _
  have pW1 : σ c A ⁻¹ᵁ W1 = (𝒲.pullback c (DualNumber A)).U1 := baseChangeSnd_preimage_U1 𝒲 c _
  have pV0 : σ c A ⁻¹ᵁ V0 = (𝒲'.pullback c (DualNumber A)).U0 := baseChangeSnd_preimage_U0 𝒲' c _
  have pV1 : σ c A ⁻¹ᵁ V1 = (𝒲'.pullback c (DualNumber A)).U1 := baseChangeSnd_preimage_U1 𝒲' c _
  have pW01 := pre_inf pW0 pW1
  have pV01 := pre_inf pV0 pV1
  have p00 := pre_inf pW0 pV0
  have p01 := pre_inf pW0 pV1
  have p10 := pre_inf pW1 pV0
  have p11 := pre_inf pW1 pV1
  have pT0 := pre_inf pW01 pV0
  have pT1 := pre_inf pW01 pV1
  have pS0 := pre_inf pW0 pV01
  have pS1 := pre_inf pW1 pV01
  have : (XA c A).IsSeparated := by
    refine ⟨?_⟩
    have hcomp : IsSeparated
        (pullback.snd c (specMap R A) ≫ terminal.from (Spec (.of A))) := inferInstance
    exact (terminal.comp_from (pullback.snd c (specMap R A))) ▸ hcomp
  have aW0 : IsAffineOpen W0 := (𝒲.pullback c A).isAffineOpen_U0
  have aW1 : IsAffineOpen W1 := (𝒲.pullback c A).isAffineOpen_U1
  have aV0 : IsAffineOpen V0 := (𝒲'.pullback c A).isAffineOpen_U0
  have aV1 : IsAffineOpen V1 := (𝒲'.pullback c A).isAffineOpen_U1
  have aW01 : IsAffineOpen (W0 ⊓ W1) := (𝒲.pullback c A).isAffineOpen_inf
  have aV01 : IsAffineOpen (V0 ⊓ V1) := (𝒲'.pullback c A).isAffineOpen_inf
  have af00 := aW0.inf aV0
  have af01 := aW0.inf aV1
  have af10 := aW1.inf aV0
  have af11 := aW1.inf aV1
  have afT0 := aW01.inf aV0
  have afT1 := aW01.inf aV1
  have afS0 := aW0.inf aV01
  have afS1 := aW1.inf aV01
  obtain ⟨u00, w00, hu00, -, huw00⟩ := exists_units_of_isFrameOn (M := N)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤
      (𝒲.pullback c (DualNumber A)).U0) (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓
      (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲'.pullback c (DualNumber A)).U0) hF0 hF0'
  obtain ⟨u01, w01, hu01, -, huw01⟩ := exists_units_of_isFrameOn (M := N)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤
      (𝒲.pullback c (DualNumber A)).U0) (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓
      (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲'.pullback c (DualNumber A)).U1) hF0 hF1'
  obtain ⟨u10, w10, hu10, -, huw10⟩ := exists_units_of_isFrameOn (M := N)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤
      (𝒲.pullback c (DualNumber A)).U1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓
      (𝒲'.pullback c (DualNumber A)).U0 ≤ (𝒲'.pullback c (DualNumber A)).U0) hF1 hF0'
  obtain ⟨u11, w11, hu11, -, huw11⟩ := exists_units_of_isFrameOn (M := N)
    (inf_le_left : (𝒲.pullback c (DualNumber A)).U1 ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤
      (𝒲.pullback c (DualNumber A)).U1) (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓
      (𝒲'.pullback c (DualNumber A)).U1 ≤ (𝒲'.pullback c (DualNumber A)).U1) hF1 hF1'
  refine ⟨lin af00 p00 u00 * cst af00 p00 w00,
    lin af01 p01 u01 * cst af01 p01 w01,
    lin af10 p10 u10 * cst af10 p10 w10,
    lin af11 p11 u11 * cst af11 p11 w11, ?_, ?_, ?_, ?_⟩
  · refine coefficient_transition_restrict af00 af10 afT0 p00 p10 pT0
      (inf_le_inf_right V0 inf_le_left) (inf_le_inf_right V0 inf_le_right)
      (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U0 inf_le_left)
      (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U0 inf_le_right)
      huw00 huw10
      (((XA c A).presheaf.map (homOfLE
        (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom f) ?_
    have h := cross_identity (M := N) hF0 (oneAddEpsMul A 𝒲 c f) hM
      u00 hu00 u10 hu10
    rw [map_oneAddEpsMul 𝒲 pW01 pT0
      (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)
      (inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓
        (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U0 ≤
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) f] at h
    exact h
  · refine coefficient_transition_restrict af01 af11 afT1 p01 p11 pT1
      (inf_le_inf_right V1 inf_le_left) (inf_le_inf_right V1 inf_le_right)
      (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U1 inf_le_left)
      (inf_le_inf_right (𝒲'.pullback c (DualNumber A)).U1 inf_le_right)
      huw01 huw11
      (((XA c A).presheaf.map (homOfLE
        (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom f) ?_
    have h := cross_identity (M := N) hF0 (oneAddEpsMul A 𝒲 c f) hM
      u01 hu01 u11 hu11
    rw [map_oneAddEpsMul 𝒲 pW01 pT1
      (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)
      (inf_le_left : ((𝒲.pullback c (DualNumber A)).U0 ⊓
        (𝒲.pullback c (DualNumber A)).U1) ⊓ (𝒲'.pullback c (DualNumber A)).U1 ≤
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) f] at h
    exact h
  · refine coefficient_transition_restrict af01 af00 afS0 p01 p00 pS0
      (inf_le_inf_left W0 inf_le_right) (inf_le_inf_left W0 inf_le_left)
      (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U0 inf_le_right)
      (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U0 inf_le_left)
      huw01 huw00
      (((XA c A).presheaf.map (homOfLE
        (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f') ?_
    have h := cross_identity' (M := N) hF0 (oneAddEpsMul A 𝒲' c f') hM'
      u00 hu00 u01 hu01
    rw [map_oneAddEpsMul 𝒲' pV01 pS0
      (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)
      (inf_le_right : (𝒲.pullback c (DualNumber A)).U0 ⊓
        ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) f'] at h
    exact h.trans (mul_comm
      (1 + eps ((𝒲.pullback c (DualNumber A)).U0 ⊓
        ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) *
        ι pS0 (((XA c A).presheaf.map (homOfLE
          (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f'))
      (((XD c A).presheaf.map (homOfLE
        (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U0 inf_le_left)).op).hom u00))
  · refine coefficient_transition_restrict af11 af10 afS1 p11 p10 pS1
      (inf_le_inf_left W1 inf_le_right) (inf_le_inf_left W1 inf_le_left)
      (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U1 inf_le_right)
      (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U1 inf_le_left)
      huw11 huw10
      (((XA c A).presheaf.map (homOfLE
        (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f') ?_
    have h := cross_identity' (M := N) hF1 (oneAddEpsMul A 𝒲' c f') hM'
      u10 hu10 u11 hu11
    rw [map_oneAddEpsMul 𝒲' pV01 pS1
      (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)
      (inf_le_right : (𝒲.pullback c (DualNumber A)).U1 ⊓
        ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) ≤
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) f'] at h
    exact h.trans (mul_comm
      (1 + eps ((𝒲.pullback c (DualNumber A)).U1 ⊓
        ((𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1)) *
        ι pS1 (((XA c A).presheaf.map (homOfLE
          (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom f'))
      (((XD c A).presheaf.map (homOfLE
        (inf_le_inf_left (𝒲.pullback c (DualNumber A)).U1 inf_le_left)).op).hom u10))

end Main

end CoverCross

end

end JacobianVarieties.Picard.Proofs.FrameCrossSections

namespace AlgebraicGeometry.RelPicard

open _root_.JacobianVarieties.Picard.Proofs.FrameCrossSections
universe u
open  _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.RelPicard
  _root_.NeronModelInfra _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.JacobianVarieties.Picard.Proofs.FrameCrossSections.CoverCross in
/-- Two frame presentations of an infinitesimal transition admit compatible cross sections. -/
theorem exists_crossSections_of_isFrameOn_of_map_eq_oneAddEpsMul_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    [IsSeparated (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))]
    (𝒲 𝒲' : C.TwoAffineOpenCover)
    (N : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Modules)
    (e₀ : Γ(N, (𝒲.pullback c (DualNumber A)).U0)) (e₁ : Γ(N, (𝒲.pullback c (DualNumber A)).U1))
    (g : ((𝒲.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀ : Scheme.Modules.IsFrameOn e₀ (𝒲.pullback c (DualNumber A)).U0)
    (h₁ : Scheme.Modules.IsFrameOn e₁ (𝒲.pullback c (DualNumber A)).U1)
    (hg : N.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲.pullback c (DualNumber A)).U0 ⊓ (𝒲.pullback c (DualNumber A)).U1) from oneAddEpsMul A
            𝒲 c g) •
        N.presheaf.map (homOfLE inf_le_left).op e₀)
    (e₀' : Γ(N, (𝒲'.pullback c (DualNumber A)).U0)) (e₁' : Γ(N, (𝒲'.pullback c (DualNumber A)).U1))
    (g' : ((𝒲'.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
    (h₀' : Scheme.Modules.IsFrameOn e₀' (𝒲'.pullback c (DualNumber A)).U0)
    (h₁' : Scheme.Modules.IsFrameOn e₁' (𝒲'.pullback c (DualNumber A)).U1)
    (hg' : N.presheaf.map (homOfLE inf_le_right).op e₁' =
      (show Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
          (𝒲'.pullback c (DualNumber A)).U0 ⊓ (𝒲'.pullback c (DualNumber A)).U1) from oneAddEpsMul
            A 𝒲' c g') •
        N.presheaf.map (homOfLE inf_le_left).op e₀') :
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
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V0 ≤ W0 ⊓ W1)).op).hom g ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_left  : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_right V1 inf_le_right : (W0 ⊓ W1) ⊓ V1 ≤ W1 ⊓
          V1)).op).hom g11
          + ((XA c A).presheaf.map (homOfLE (inf_le_left : (W0 ⊓ W1) ⊓ V1 ≤ W0 ⊓ W1)).op).hom g ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
        V1)).op).hom g01
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W0 inf_le_left  : W0 ⊓ (V0 ⊓ V1) ≤ W0 ⊓
          V0)).op).hom g00
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W0 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' ∧
      ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
        V1)).op).hom g11
        = ((XA c A).presheaf.map (homOfLE (inf_le_inf_left W1 inf_le_left  : W1 ⊓ (V0 ⊓ V1) ≤ W1 ⊓
          V0)).op).hom g10
          + ((XA c A).presheaf.map (homOfLE (inf_le_right : W1 ⊓ (V0 ⊓ V1) ≤ V0 ⊓ V1)).op).hom g' :=
  CoverCross.main c A 𝒲 𝒲' N e₀ e₁ g h₀ h₁ hg e₀' e₁' g' h₀' h₁' hg'
end AlgebraicGeometry.RelPicard
end ProofImplementation
