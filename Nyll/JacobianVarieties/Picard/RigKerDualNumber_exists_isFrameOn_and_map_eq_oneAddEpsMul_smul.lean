/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Ring.Equiv
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Opposites
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.Basic
import Nyll.JacobianVarieties.Picard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_exists_isUnit_map_eq_mul_of_iso_tensorUnit
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul
import Nyll.JacobianVarieties.Picard.Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction
import Nyll.SchemeTheory.Modules.FrameFromTrivialization

/-!
# Local frames and normalized transitions over the dual numbers
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DualNumberFrame
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

open scoped TensorProduct

namespace PicTanF

section Frames

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- Restriction along the identity inclusion fixes a section. -/
theorem map_homOfLE_refl (s : Γ(M, U)) : M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, M.presheaf.map_id]
  rfl

/-- Two frames on the same open differ by inverse scalar factors. -/
theorem exists_smul_eq_of_isFrameOn {s s' : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s U)
    (hs' : Scheme.Modules.IsFrameOn s' U) :
    ∃ v w : Γ(X, U), v • s = s' ∧ w • s' = s ∧ v * w = 1 := by
  obtain ⟨v, hv⟩ := (hs (le_refl U) (le_refl U)).2 s'
  obtain ⟨w, hw⟩ := (hs' (le_refl U) (le_refl U)).2 s
  simp only [map_homOfLE_refl] at hv hw
  refine ⟨v, w, hv, hw, ?_⟩
  apply (hs (le_refl U) (le_refl U)).1
  simp only [map_homOfLE_refl]
  rw [mul_comm, mul_smul, hv, hw, one_smul]

/-- A frame allows cancellation of a scalar after restriction. -/
theorem smul_left_cancel_of_isFrameOn {V W : X.Opens} {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) {g g' : Γ(X, W)}
    (h : g • M.presheaf.map (homOfLE hWU).op s = g' • M.presheaf.map (homOfLE hWU).op s) : g = g' :=
  (hs hWU hWV).1 h

end Frames

end PicTanF

namespace PicTanF

section Split

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {Bε : Type u} [CommRing Bε] [Algebra (DualNumber A) Bε]

/-- The constant and infinitesimal coefficients of a tensor over the dual numbers. -/
noncomputable def coords : DualNumber A ⊗[A] B →ₗ[A] B × B :=
  TensorProduct.lift
    { toFun := fun d => (TrivSqZeroExt.fst d • LinearMap.id (R := A) (M := B)).prod
        (TrivSqZeroExt.snd d • LinearMap.id (R := A) (M := B))
      map_add' := fun d d' => by
        apply LinearMap.ext
        intro b
        apply Prod.ext
        · change (d + d').fst • b = d.fst • b + d'.fst • b
          rw [TrivSqZeroExt.fst_add, add_smul]
        · change (d + d').snd • b = d.snd • b + d'.snd • b
          rw [TrivSqZeroExt.snd_add, add_smul]
      map_smul' := fun a d => by
        apply LinearMap.ext
        intro b
        apply Prod.ext
        · change (a • d).fst • b = a • (d.fst • b)
          rw [TrivSqZeroExt.fst_smul, smul_eq_mul, mul_smul]
        · change (a • d).snd • b = a • (d.snd • b)
          rw [TrivSqZeroExt.snd_smul, smul_eq_mul, mul_smul] }

/-- The tensor coordinates are the constant and epsilon coefficients. -/
@[scoped simp] theorem coords_tmul (d : DualNumber A) (b : B) :
    coords (d ⊗ₜ[A] b) = (TrivSqZeroExt.fst d • b, TrivSqZeroExt.snd d • b) := by
  rfl

/-- A pure tensor splits into its constant and infinitesimal parts. -/
theorem tmul_eq (d : DualNumber A) (b : B) :
    d ⊗ₜ[A] b = (1 : DualNumber A) ⊗ₜ[A] (TrivSqZeroExt.fst d • b) +
      (DualNumber.eps : DualNumber A) • ((1 : DualNumber A) ⊗ₜ[A] (TrivSqZeroExt.snd d • b)) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul, ←
    TensorProduct.smul_tmul,
    ← TensorProduct.add_tmul]
  congr 1
  refine TrivSqZeroExt.ext ?_ ?_ <;>
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, DualNumber.fst_eps, DualNumber.snd_eps,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]

/-- The chart equivalence expresses every section in two dual-number coefficients. -/
theorem exists_eq (e : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B → Bε)
    (hι : ∀ s, e ((1 : DualNumber A) ⊗ₜ[A] s) = ι s)
    (z : Bε) : ∃ x y : B, z = ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y := by
  obtain ⟨t, rfl⟩ := e.surjective z
  induction t using TensorProduct.inductionOn with
  | tmul d b =>
    refine ⟨TrivSqZeroExt.fst d • b, TrivSqZeroExt.snd d • b, ?_⟩
    rw [tmul_eq d b, map_add, map_smul, hι, hι]
    congr 1
    exact Algebra.smul_def _ _
  | add t t' ht ht' =>
    obtain ⟨x, y, hx⟩ := ht
    obtain ⟨x', y', hx'⟩ := ht'
    refine ⟨x + x', y + y', ?_⟩
    have hadd : ∀ a b : B, ι (a + b) = ι a + ι b := fun a b => by
      rw [← hι, ← hι, ← hι, TensorProduct.tmul_add, map_add]
    rw [map_add, hx, hx', hadd, hadd]
    ring

/-- The two coefficients of a section in the chart presentation are unique. -/
theorem unique (e : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B → Bε)
    (hι : ∀ s, e ((1 : DualNumber A) ⊗ₜ[A] s) = ι s) {x y x' y' : B}
    (h : ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y =
      ι x' + algebraMap (DualNumber A) Bε DualNumber.eps * ι y') :
    x = x' ∧ y = y' := by
  have key : ∀ a b : B, e ((1 : DualNumber A) ⊗ₜ[A] a + (DualNumber.eps : DualNumber A) ⊗ₜ[A] b) =
      ι a + algebraMap (DualNumber A) Bε DualNumber.eps * ι b := fun a b => by
    rw [map_add, show (DualNumber.eps : DualNumber A) ⊗ₜ[A] b =
        (DualNumber.eps : DualNumber A) • ((1 : DualNumber A) ⊗ₜ[A] b) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, hι, hι, Algebra.smul_def]
  rw [← key, ← key] at h
  have h2 := congrArg coords (e.injective h)
  simp only [map_add, coords_tmul, TrivSqZeroExt.fst_one, one_smul, TrivSqZeroExt.snd_one,
    zero_smul,
    DualNumber.fst_eps, DualNumber.snd_eps, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq] at h2
  exact h2

omit [Algebra A B] in
/-- Multiplication in a dual-number presentation satisfies the square-zero product formula. -/
theorem mul_eq (ι : B →+* Bε) (x y x' y' : B) :
    (ι x + algebraMap (DualNumber A) Bε DualNumber.eps * ι y) *
      (ι x' + algebraMap (DualNumber A) Bε DualNumber.eps * ι y') =
    ι (x * x') + algebraMap (DualNumber A) Bε DualNumber.eps * ι (x * y' + x' * y) := by
  have he : algebraMap (DualNumber A) Bε DualNumber.eps * algebraMap (DualNumber A) Bε
    DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  simp only [map_mul, map_add]
  linear_combination (ι y * ι y') * he

end Split

section Indep

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙
  (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- The first chart ring map induced by the dual-number thickening. -/
noncomputable def ι0 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).U0_le).hom
/-- The second chart ring map induced by the dual-number thickening. -/
noncomputable def ι1 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).U1_le).hom
/-- The overlap ring map induced by the dual-number thickening. -/
noncomputable def ι01 : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 →+*
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 :=
  ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le).hom

/-- The first chart component is the restricted thickening map. -/
theorem map0_eq
    (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) : (dualNumberThickening A 𝒱
      c).map0 x = ι0 c A 𝒱 x := rfl
/-- The second chart component is the restricted thickening map. -/
theorem map1_eq
    (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) : (dualNumberThickening A 𝒱
      c).map1 x = ι1 c A 𝒱 x := rfl
/-- The overlap component is the restricted thickening map. -/
theorem map01_eq
    (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) : (dualNumberThickening A 𝒱
      c).map01 x = ι01 c A 𝒱 x := rfl

/-- The transition multiplier is one plus its infinitesimal coefficient. -/
theorem oneAddEpsMul_eq
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) : oneAddEpsMul A 𝒱 c f =
    ι01 c A 𝒱 1 + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 f := by
  rw [map_one]; rfl

/-- The chart and overlap section rings admit the scalar-extension presentations. -/
theorem exists_splittings :
    ∃ (e0 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0
      ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0)
      (e1 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1
        ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1)
      (e01 : DualNumber A ⊗[A] ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01
        ≃ₐ[DualNumber A]
          ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01),
      (∀ s, e0 ((1 : DualNumber A) ⊗ₜ[A] s) = ι0 c A 𝒱 s) ∧ (∀ s, e1 ((1 : DualNumber A) ⊗ₜ[A] s) =
        ι1 c A 𝒱 s) ∧
      (∀ s, e01 ((1 : DualNumber A) ⊗ₜ[A] s) = ι01 c A 𝒱 s) := by
  obtain ⟨e0, e1, e01, h0, h1, h01⟩ :=
    Scheme.TwoAffineOpenCover.exists_stage_baseChangeIsos_structureSheaf 𝒱 c A (DualNumber A)
  exact ⟨e0, e1, e01, fun s => h0 s, fun s => h1 s, fun s => h01 s⟩

end Indep

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF

section Main

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙
  (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- A pair of chart frames with transition multiplier one plus the infinitesimal overlap
coefficient. -/
def IsSystem (M : RigKerDualNumber.Carrier c ε A)
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) : Prop :=
  ∃ (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber
    A)).U1)),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 ∧
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 ∧
    M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
          (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from oneAddEpsMul A
            𝒱 c f) •
        M.1.L.presheaf.map (homOfLE inf_le_left).op e₀

/-- Restriction from the first chart is the first map of the two-chart cover. -/
theorem res_U0_eq
    (v : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0)) :
    (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
      (homOfLE (inf_le_left : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1 ≤
        _)).op v =
    (show Γ(Limits.pullback c (specMap R (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0 v) := rfl
/-- Restriction from the second chart is the second map of the two-chart cover. -/
theorem res_U1_eq
    (v : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1)) :
    (Limits.pullback c (specMap R (DualNumber A))).presheaf.map
      (homOfLE (inf_le_right : (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1
        ≤ _)).op v =
    (show Γ(Limits.pullback c (specMap R (DualNumber A)),
        (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1) from
      ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1 v) := rfl

/-- Restriction from the first chart preserves both coefficients. -/
theorem ρ0_split (a b : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ0
        (ι0 c A 𝒱 a + algebraMap (DualNumber A) _ DualNumber.eps * ι0 c A 𝒱 b) =
      ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ0 a) +
        algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover
          (pullback.snd c (specMap R A))).ρ0 b) := by
  rw [map_add, map_mul, AlgHom.commutes, ← map0_eq, ← map0_eq, ← HomOver.map01_ρ0,
    ← HomOver.map01_ρ0]
  rfl

/-- Restriction from the second chart preserves both coefficients. -/
theorem ρ1_split (a b : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).ρ1
        (ι1 c A 𝒱 a + algebraMap (DualNumber A) _ DualNumber.eps * ι1 c A 𝒱 b) =
      ι01 c A 𝒱 (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ρ1 a) +
        algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 (((𝒱.pullback c A).cover
          (pullback.snd c (specMap R A))).ρ1 b) := by
  rw [map_add, map_mul, AlgHom.commutes, ← map1_eq, ← map1_eq, ← HomOver.map01_ρ1,
    ← HomOver.map01_ρ1]
  rfl

end Main

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF

section Red

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- The morphism of two-chart covers induced by reduction of the dual numbers. -/
noncomputable abbrev red :
    HomOver (TrivSqZeroExt.fstHom R A A).toRingHom (𝒱.pullback c (DualNumber A))
      (pullback.snd c (specMap R (DualNumber A))) (𝒱.pullback c A) (pullback.snd c (specMap R A)) :=
  HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)

/-- The reduction morphism is the base-change map induced by the constant coefficient. -/
theorem red_hom_eq : (red c A 𝒱).hom = RelPicard.baseChangeSnd c (dualNumberReductionOver R A) :=
  rfl

/-- The overlap ring map induced by reduction of the dual numbers. -/
noncomputable def r01 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber
  A)))).A01 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).inf_le).hom

/-- The overlap component of reduction is the restricted reduction map. -/
theorem red_map01_eq
    (x : ((𝒱.pullback c (DualNumber A)).cover
      (pullback.snd c (specMap R (DualNumber A)))).A01) : (red c A 𝒱).map01 x = r01 c A 𝒱 x := rfl

/-- Reduction followed by the thickening projection is the identity. -/
theorem red_comp_thickening : (red c A 𝒱).hom ≫ (dualNumberThickening A 𝒱 c).hom = 𝟙 _ := by
  change RelPicard.baseChangeSnd c (LFP.stageHom R (TrivSqZeroExt.fstHom R A A)) ≫
      RelPicard.baseChangeSnd c (LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A))) = 𝟙 _
  rw [RelPicard.baseChangeSnd_comp, ← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- The overlap reduction recovers a constant section. -/
theorem r01_ι01 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    r01 c A 𝒱 (ι01 c A 𝒱 x) = x := by
  change ((dualNumberThickening A 𝒱 c).hom.appLE _ _ (dualNumberThickening A 𝒱 c).inf_le ≫
    (red c A 𝒱).hom.appLE _ _ (red c A 𝒱).inf_le).hom x = x
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ : Limits.pullback c (specMap R A) ⟶ Limits.pullback c (specMap R A)), φ = 𝟙 _ →
      ∀ (e : (𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1 ≤ φ ⁻¹ᵁ ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c
        A).U1)),
      (φ.appLE _ _ e).hom x = x := by
    rintro _ rfl e
    have hid : (𝟙 (Limits.pullback c (specMap R A)) : _ ⟶ _).appLE _ _ e = 𝟙 _ := by
      change (𝟙 _ : Limits.pullback c (specMap R A) ⟶ _).app _ ≫ (Limits.pullback c (specMap R
        A)).presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg (Limits.pullback c (specMap R A)).presheaf.map (Subsingleton.elim _ _)).trans
        ((Limits.pullback c (specMap R A)).presheaf.map_id _)
    rw [hid]
    rfl
  exact key _ (red_comp_thickening c A 𝒱) _

/-- The overlap reduction kills epsilon. -/
theorem r01_eps : r01 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).inf_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from
    DualNumber.fst_eps,
    map_zero] at h
  exact h

/-- The overlap reduction returns the constant coefficient. -/
theorem r01_split (x y : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    r01 c A 𝒱 (ι01 c A 𝒱 x + algebraMap (DualNumber A) _ DualNumber.eps * ι01 c A 𝒱 y) = x := by
  rw [map_add, map_mul, r01_ι01, r01_eps, zero_mul, add_zero]

end Red

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF

section DualChart

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {Bε : Type u} [CommRing Bε] [Algebra (DualNumber A) Bε]
  (E : DualNumber A ⊗[A] B ≃ₐ[DualNumber A] Bε) (ι : B →+* Bε)
  (hι : ∀ s, E ((1 : DualNumber A) ⊗ₜ[A] s) = ι s)

/-- The chart ring homomorphism sending the two coefficients to the constant and infinitesimal
parts. -/
noncomputable def ofDualNumber : DualNumber B →+* Bε where
  toFun d := ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι d.snd
  map_one' := by
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_one, map_zero, mul_zero, add_zero]
  map_mul' d d' := by
    rw [mul_eq ι]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
      MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    congr 3
    ring
  map_zero' := by
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, mul_zero, add_zero]
  map_add' d d' := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]
    ring

omit [Algebra A B] in
/-- The chart homomorphism evaluates the constant and epsilon coefficients. -/
theorem ofDualNumber_apply (d : DualNumber B) :
    ofDualNumber (A := A) ι d = ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι d.snd :=
      rfl

include hι in
/-- The chart homomorphism is bijective by existence and uniqueness of coefficients. -/
theorem ofDualNumber_bijective : Function.Bijective (ofDualNumber (A := A) ι) := by
  constructor
  · intro d d' h
    rw [ofDualNumber_apply, ofDualNumber_apply] at h
    obtain ⟨h1, h2⟩ := unique E ι hι h
    exact TrivSqZeroExt.ext h1 h2
  · intro z
    obtain ⟨x, y, rfl⟩ := exists_eq E ι hι z
    refine ⟨TrivSqZeroExt.inl x + TrivSqZeroExt.inr y, ?_⟩
    rw [ofDualNumber_apply, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- The ring equivalence recovering the two dual-number coefficients from the chart presentation. -/
noncomputable def dualChartEquiv : Bε ≃+* DualNumber B :=
  (RingEquiv.ofBijective (ofDualNumber (A := A) ι) (ofDualNumber_bijective E ι hι)).symm

/-- The inverse chart equivalence evaluates the two coefficients. -/
theorem dualChartEquiv_symm_apply (d : DualNumber B) :
    (dualChartEquiv E ι hι).symm d = ι d.fst + algebraMap (DualNumber A) Bε DualNumber.eps * ι
      d.snd := rfl

/-- A constant section has zero infinitesimal coefficient. -/
theorem dualChartEquiv_ι (s : B) : dualChartEquiv E ι hι (ι s) = TrivSqZeroExt.inl s := by
  apply (dualChartEquiv E ι hι).symm.injective
  rw [RingEquiv.symm_apply_apply, dualChartEquiv_symm_apply,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero, mul_zero, add_zero]

/-- The chart equivalence preserves epsilon. -/
theorem dualChartEquiv_eps :
    dualChartEquiv E ι hι (algebraMap (DualNumber A) Bε DualNumber.eps) = DualNumber.eps := by
  apply (dualChartEquiv E ι hι).symm.injective
  rw [RingEquiv.symm_apply_apply, dualChartEquiv_symm_apply,
    DualNumber.fst_eps, DualNumber.snd_eps, map_zero, map_one, mul_one, zero_add]

/-- The first coordinate of the chart equivalence is reduction. -/
theorem fst_dualChartEquiv (r : Bε →+* B) (hrι : ∀ x, r (ι x) = x)
    (hre : r (algebraMap (DualNumber A) Bε DualNumber.eps) = 0) (z : Bε) :
    (dualChartEquiv E ι hι z).fst = r z := by
  obtain ⟨x, y, rfl⟩ := exists_eq E ι hι z
  rw [map_add, map_mul, dualChartEquiv_ι, dualChartEquiv_ι, dualChartEquiv_eps, map_add, map_mul,
    hrι, hrι, hre,
    zero_mul, add_zero]
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_mul,
    DualNumber.fst_eps, zero_mul, add_zero]

/-- Composing the chart equivalence with the first projection gives reduction. -/
theorem fstHom_comp_dualChartEquiv (r : Bε →+* B) (hrι : ∀ x, r (ι x) = x)
    (hre : r (algebraMap (DualNumber A) Bε DualNumber.eps) = 0) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualChartEquiv E ι hι).toRingHom = r :=
  RingHom.ext fun z => fst_dualChartEquiv E ι hι r hrι hre z

/-- The chart equivalence sends the constant map to the dual-number inclusion. -/
theorem dualChartEquiv_comp_ι :
    (dualChartEquiv E ι hι).toRingHom.comp ι = (TrivSqZeroExt.inlHom B B : B →+* DualNumber B) :=
  RingHom.ext fun s => dualChartEquiv_ι E ι hι s

end DualChart

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF

section RedCharts

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- The first chart ring map induced by reduction of the dual numbers. -/
noncomputable def r0 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber
  A)))).A0 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).U0_le).hom

/-- The second chart ring map induced by reduction of the dual numbers. -/
noncomputable def r1 : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber
  A)))).A1 →+*
    ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1 :=
  ((red c A 𝒱).hom.appLE _ _ (red c A 𝒱).U1_le).hom

/-- The first chart reduction acts by its restricted section map. -/
theorem r0_apply
    (z : ((𝒱.pullback c (DualNumber A)).cover
      (pullback.snd c (specMap R (DualNumber A)))).A0) : r0 c A 𝒱 z = ((HomOver.stage 𝒱 c
        (TrivSqZeroExt.fstHom R A A)).hom.appLE
    ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U0_le).hom z := rfl

/-- The second chart reduction acts by its restricted section map. -/
theorem r1_apply
    (z : ((𝒱.pullback c (DualNumber A)).cover
      (pullback.snd c (specMap R (DualNumber A)))).A1) : r1 c A 𝒱 z = ((HomOver.stage 𝒱 c
        (TrivSqZeroExt.fstHom R A A)).hom.appLE
    ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
    (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U1_le).hom z := rfl

/-- Reduction recovers a section after its pullback through the thickening. -/
theorem red_thickening_appLE {U : (Limits.pullback c (specMap R A)).Opens}
    {V : (Limits.pullback c (specMap R (DualNumber A))).Opens}
    (h₁ : V ≤ (dualNumberThickening A 𝒱 c).hom ⁻¹ᵁ U)
    (h₂ : U ≤ (red c A 𝒱).hom ⁻¹ᵁ V) (x : Γ(Limits.pullback c (specMap R A), U)) :
    ((red c A 𝒱).hom.appLE V U h₂).hom (((dualNumberThickening A 𝒱 c).hom.appLE U V h₁).hom x) = x
      := by
  change ((dualNumberThickening A 𝒱 c).hom.appLE U V h₁ ≫ (red c A 𝒱).hom.appLE V U h₂).hom x = x
  rw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (φ : Limits.pullback c (specMap R A) ⟶ Limits.pullback c (specMap R A)), φ = 𝟙 _ →
      ∀ (e : U ≤ φ ⁻¹ᵁ U), (φ.appLE _ _ e).hom x = x := by
    rintro _ rfl e
    have hid : (𝟙 (Limits.pullback c (specMap R A)) : _ ⟶ _).appLE _ _ e = 𝟙 _ := by
      change (𝟙 _ : Limits.pullback c (specMap R A) ⟶ _).app _ ≫ (Limits.pullback c (specMap R
        A)).presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg (Limits.pullback c (specMap R A)).presheaf.map (Subsingleton.elim _ _)).trans
        ((Limits.pullback c (specMap R A)).presheaf.map_id _)
    rw [hid]
    rfl
  exact key _ (red_comp_thickening c A 𝒱) _

/-- The first chart reduction recovers a constant section. -/
theorem r0_ι0 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0) :
    r0 c A 𝒱 (ι0 c A 𝒱 x) = x :=
  red_thickening_appLE c A 𝒱 (U := (𝒱.pullback c A).U0) (dualNumberThickening A 𝒱 c).U0_le (red c A
    𝒱).U0_le x

/-- The second chart reduction recovers a constant section. -/
theorem r1_ι1 (x : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1) :
    r1 c A 𝒱 (ι1 c A 𝒱 x) = x :=
  red_thickening_appLE c A 𝒱 (U := (𝒱.pullback c A).U1) (dualNumberThickening A 𝒱 c).U1_le (red c A
    𝒱).U1_le x

/-- The first chart reduction kills epsilon. -/
theorem r0_eps : r0 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).U0_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from
    DualNumber.fst_eps,
    map_zero] at h
  exact h

/-- The second chart reduction kills epsilon. -/
theorem r1_eps : r1 c A 𝒱 (algebraMap (DualNumber A) _ DualNumber.eps) = 0 := by
  have h := (red c A 𝒱).appLE_algebraMap (red c A 𝒱).U1_le (DualNumber.eps : DualNumber A)
  rw [show (TrivSqZeroExt.fstHom R A A).toRingHom (DualNumber.eps : DualNumber A) = 0 from
    DualNumber.fst_eps,
    map_zero] at h
  exact h

/-- The first chart admits a dual-number presentation compatible with reduction. -/
theorem exists_ringEquiv_dualNumber_chart0 :
    ∃ θ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A0 ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0),
      (∀ z, (θ z).fst = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
          ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
          (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U0_le).hom z) ∧
      (∀ s, θ (ι0 c A 𝒱 s) = TrivSqZeroExt.inl s) ∧
      θ (algebraMap (DualNumber A) _ DualNumber.eps) = DualNumber.eps := by
  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  exact ⟨dualChartEquiv E0 (ι0 c A 𝒱) hE0,
    fst_dualChartEquiv E0 (ι0 c A 𝒱) hE0 (r0 c A 𝒱) (r0_ι0 c A 𝒱) (r0_eps c A 𝒱),
    dualChartEquiv_ι E0 (ι0 c A 𝒱) hE0, dualChartEquiv_eps E0 (ι0 c A 𝒱) hE0⟩

/-- The second chart admits a dual-number presentation compatible with reduction. -/
theorem exists_ringEquiv_dualNumber_chart1 :
    ∃ θ : ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A1 ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1),
      (∀ z, (θ z).fst = ((HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).hom.appLE
          ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
          (HomOver.stage 𝒱 c (TrivSqZeroExt.fstHom R A A)).U1_le).hom z) ∧
      (∀ s, θ (ι1 c A 𝒱 s) = TrivSqZeroExt.inl s) ∧
      θ (algebraMap (DualNumber A) _ DualNumber.eps) = DualNumber.eps := by
  obtain ⟨E0, E1, E01, hE0, hE1, hE01⟩ := exists_splittings c A 𝒱
  exact ⟨dualChartEquiv E1 (ι1 c A 𝒱) hE1,
    fst_dualChartEquiv E1 (ι1 c A 𝒱) hE1 (r1 c A 𝒱) (r1_ι1 c A 𝒱) (r1_eps c A 𝒱),
    dualChartEquiv_ι E1 (ι1 c A 𝒱) hE1, dualChartEquiv_eps E1 (ι1 c A 𝒱) hE1⟩

end RedCharts

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF

section FrameHelpers

variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens}

/-- Multiplication by a unit preserves a frame. -/
theorem isFrameOn_smul {s : Γ(M, U)} (hs : Scheme.Modules.IsFrameOn s V) {u : Γ(X, U)}
    (hu : IsUnit u) :
    Scheme.Modules.IsFrameOn (u • s) V := by
  intro W hWU hWV
  have e : M.presheaf.map (homOfLE hWU).op (u • s) =
      X.presheaf.map (homOfLE hWU).op u • M.presheaf.map (homOfLE hWU).op s :=
        Scheme.Modules.map_smul _ _ _ _
  have : (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op (u • s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘
        (fun g : Γ(X, W) => g * X.presheaf.map (homOfLE hWU).op u) := by
    funext g
    simp only [Function.comp_apply, e, mul_smul]
  rw [this]
  exact (hs hWU hWV).comp (Units.mulRight (hu.map (X.presheaf.map (homOfLE
    hWU).op).hom).unit).bijective

end FrameHelpers

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF1S

section Yoga

variable {X Y Z : Scheme.{u}}

/-- Triviality of a pullback persists after a further pullback. -/
theorem pullback_comp_unit (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (g ≫ f)).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackComp g f).app M).symm ≪≫ (Scheme.Modules.pullback g).mapIso h.some ≪≫
    Scheme.Modules.pullbackUnitIso g⟩

/-- Equal morphisms give the same pullback triviality. -/
theorem pullback_congr_unit {f f' : Y ⟶ X} (hf : f = f') (M : X.Modules)
    (h : Nonempty ((Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackCongr hf).app M).symm ≪≫ h.some⟩

/-- Triviality after pullback along an isomorphism implies triviality. -/
theorem unit_of_pullback_iso_inv (α : Y ≅ Z) (N : Y.Modules)
    (h : Nonempty ((Scheme.Modules.pullback α.inv).obj N ≅ SheafOfModules.unit Z.ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit Y.ringCatSheaf) :=
  ⟨((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    ((Scheme.Modules.pullbackCongr α.hom_inv_id).app N).symm ≪≫
    ((Scheme.Modules.pullbackComp α.hom α.inv).app N).symm ≪≫
    (Scheme.Modules.pullback α.hom).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso α.hom⟩

end Yoga

attribute [local simp] PicTanF.coords_tmul

section Chart

variable {X X₀ : Scheme.{u}}

/-- An invertible module with trivial reduction is trivial on a dual-number affine chart. -/
theorem nonempty_pullback_ι_iso_unit (red : X₀ ⟶ X) (M : X.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hU : IsAffineOpen U) (U₀ : X₀.Opens) (hU₀ : IsAffineOpen U₀) (hle : U₀ ≤ red ⁻¹ᵁ
      U)
    (h0 : Nonempty ((Scheme.Modules.pullback red).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf))
    (θ : Γ(X, U) ≃+* DualNumber Γ(X₀, U₀))
    (hθ : ∀ z, TrivSqZeroExt.fst (θ z) = (red.appLE U U₀ hle).hom z) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U :
      Scheme.{u}).ringCatSheaf) := by
  let φ : Γ(X, U) ⟶ CommRingCat.of (DualNumber Γ(X₀, U₀)) := CommRingCat.ofHom θ.toRingHom
  let ψ : CommRingCat.of (DualNumber Γ(X₀, U₀)) ⟶ Γ(X, U) := CommRingCat.ofHom θ.symm.toRingHom
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => θ.symm_apply_apply x
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply CommRingCat.hom_ext
    exact RingHom.ext fun x => θ.apply_symm_apply x
  let α : (U : Scheme.{u}) ≅ Spec (CommRingCat.of (DualNumber Γ(X₀, U₀))) :=
    hU.isoSpec ≪≫ ⟨Spec.map ψ, Spec.map φ,
      by rw [← Spec.map_comp, hφψ, Spec.map_id],
      by rw [← Spec.map_comp, hψφ, Spec.map_id]⟩
  let M' : (Spec (CommRingCat.of (DualNumber Γ(X₀, U₀)))).Modules := (Scheme.Modules.pullback
    (α.inv ≫ U.ι)).obj M
  have hM' : Scheme.Modules.IsInvertible M' := hM.pullback _
  have hsq : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X₀, U₀) Γ(X₀, U₀) Γ(X₀,
    U₀)).toRingHom) ≫
      α.inv ≫ U.ι = hU₀.fromSpec ≫ red := by
    have hα : α.inv ≫ U.ι = Spec.map φ ≫ hU.fromSpec := by
      change (Spec.map φ ≫ hU.isoSpec.inv) ≫ U.ι = _
      rw [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
    rw [hα, ← Category.assoc, ← Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec red hU hU₀ hle]
    congr 2
    ext z
    change TrivSqZeroExt.fst (θ z) = _
    exact hθ z
  have h0' : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Γ(X₀, U₀) Γ(X₀, U₀) Γ(X₀,
        U₀)).toRingHom))).obj M' ≅
        SheafOfModules.unit (Spec (CommRingCat.of Γ(X₀, U₀))).ringCatSheaf) := by
    refine ⟨((Scheme.Modules.pullbackComp _ _).app M) ≪≫ ?_⟩
    refine (pullback_congr_unit hsq.symm M ?_).some
    rw [← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
    exact pullback_comp_unit _ _ M (pullback_comp_unit _ _ M h0)
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_unit_of_dualNumber_of_reduction Γ(X₀, U₀)
    M' hM' h0'
  exact unit_of_pullback_iso_inv α _ ⟨((Scheme.Modules.pullbackComp α.inv U.ι).app M).symm.symm ≪≫
    e⟩

end Chart

attribute [local simp] PicTanF.coords_tmul

end PicTanF1S

attribute [local simp] PicTanF.coords_tmul

namespace PicTanF1S

section F1

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

/-- The first chart admits a dual-number presentation compatible with reduction. -/
private theorem exists_ringEquiv_dualNumber_chart0 :
    ∃ θ : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U0) ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A0),
      ∀ z, TrivSqZeroExt.fst (θ z) =
        ((RelPicard.baseChangeSnd c (dualNumberReductionOver R A)).appLE
          ((𝒱.pullback c (DualNumber A)).U0) ((𝒱.pullback c A).U0)
          (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (dualNumberReductionOver R
            A)).ge).hom z := by
  obtain ⟨θ, h, -, -⟩ := PicTanF.exists_ringEquiv_dualNumber_chart0 c A 𝒱
  exact ⟨θ, h⟩

/-- The second chart admits a dual-number presentation compatible with reduction. -/
private theorem exists_ringEquiv_dualNumber_chart1 :
    ∃ θ : Γ(Limits.pullback c (specMap R (DualNumber A)), (𝒱.pullback c (DualNumber A)).U1) ≃+*
        DualNumber (((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A1),
      ∀ z, TrivSqZeroExt.fst (θ z) =
        ((RelPicard.baseChangeSnd c (dualNumberReductionOver R A)).appLE
          ((𝒱.pullback c (DualNumber A)).U1) ((𝒱.pullback c A).U1)
          (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (dualNumberReductionOver R
            A)).ge).hom z := by
  obtain ⟨θ, h, -, -⟩ := PicTanF.exists_ringEquiv_dualNumber_chart1 c A 𝒱
  exact ⟨θ, h⟩

end F1

attribute [local simp] PicTanF.coords_tmul

end PicTanF1S

attribute [local simp] PicTanF.coords_tmul

open PicTanF1S in
/-- An invertible module with trivial reduction has a frame on each affine chart. -/
theorem F1_chartTrivial
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)
    (M : (Limits.pullback c (specMap R (DualNumber A))).Modules) (hM : Scheme.Modules.IsInvertible
      M)
    (h0 : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver R
      A))).obj M ≅ 𝟙_ _)) :
    (∃ e₀ : Γ(M, (𝒱.pullback c (DualNumber A)).U0), Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c
      (DualNumber A)).U0) ∧
    (∃ e₁ : Γ(M, (𝒱.pullback c (DualNumber A)).U1), Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c
      (DualNumber A)).U1) := by
  have h0' : Nonempty ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (dualNumberReductionOver
    R A))).obj M ≅
      SheafOfModules.unit.{u} (Limits.pullback c (specMap R A)).ringCatSheaf) := h0
  constructor
  · obtain ⟨θ, hθ⟩ := exists_ringEquiv_dualNumber_chart0 c A 𝒱
    obtain ⟨e⟩ := nonempty_pullback_ι_iso_unit (RelPicard.baseChangeSnd c (dualNumberReductionOver
      R A)) M hM
      ((𝒱.pullback c (DualNumber A)).U0) (𝒱.pullback c (DualNumber A)).isAffineOpen_U0
      ((𝒱.pullback c A).U0) (𝒱.pullback c A).isAffineOpen_U0
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (dualNumberReductionOver R A)).ge
        h0' θ hθ
    exact Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit _ e
  · obtain ⟨θ, hθ⟩ := exists_ringEquiv_dualNumber_chart1 c A 𝒱
    obtain ⟨e⟩ := nonempty_pullback_ι_iso_unit (RelPicard.baseChangeSnd c (dualNumberReductionOver
      R A)) M hM
      ((𝒱.pullback c (DualNumber A)).U1) (𝒱.pullback c (DualNumber A)).isAffineOpen_U1
      ((𝒱.pullback c A).U1) (𝒱.pullback c A).isAffineOpen_U1
      (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (dualNumberReductionOver R A)).ge
        h0' θ hθ
    exact Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit _ e

namespace PicTanF

section Frames2

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙
  (Spec (.of R))) c)
  (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

local notation "Xε" => Limits.pullback c (specMap R (DualNumber A))
local notation "XA" => Limits.pullback c (specMap R A)

/-- A rigidified deformation admits a normalized system of local frames. -/
theorem exists_isSystem (M : RigKerDualNumber.Carrier c ε A) : ∃ f, IsSystem c ε A 𝒱 M f := by
  obtain ⟨e₀, e₁, f, h₀, h₁, h⟩ :=
    RelPicard.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul_of_nonempty_pullback_iso_unit
      c A 𝒱 M.1.L M.1.isInvertible M.2
  exact ⟨f, e₀, e₁, h₀, h₁, h⟩

end Frames2

attribute [local simp] PicTanF.coords_tmul

end PicTanF

attribute [local simp] PicTanF.coords_tmul

end JacobianVarieties.Picard.Proofs.DualNumberFrame

namespace AlgebraicGeometry.RelPicard.RigKerDualNumber

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.TwoAffineOpenCover
open JacobianVarieties.Picard.Proofs.DualNumberFrame

/-- A rigidified deformation has two local frames with a normalized infinitesimal transition. -/
theorem exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c)
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (M :
      RigKerDualNumber.Carrier c ε A) :
    ∃ (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber
      A)).U1))
      (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
      Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 ∧
      Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 ∧
      M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
        (show Γ(Limits.pullback c (specMap R (DualNumber A)),
                (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
            from oneAddEpsMul A 𝒱 c f) • M.1.L.presheaf.map (homOfLE inf_le_left).op e₀ := by
  obtain ⟨f, e₀, e₁, h₀, h₁, h⟩ := PicTanF.exists_isSystem c ε A 𝒱 M
  exact ⟨e₀, e₁, f, h₀, h₁, h⟩
end AlgebraicGeometry.RelPicard.RigKerDualNumber
end ProofImplementation

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
