/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom

/-!
# Scheme Modules exists hom tensor Pow three support zero Scheme Ideal eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

universe u

section translate_product
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace TPSol

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk
  t)]

/-- Translation of the group scheme by the indicated point. -/
noncomputable abbrev T (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left

theorem T_inv_mul (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : T t (y⁻¹ * y) = 𝟙 X :=
  by
  have h1 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) = 𝟙 (Over.mk t) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc, GrpObj.comp_inv, inv_mul_cancel, mul_one]
  have h2 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) =
      𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (y⁻¹ * y)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc]
    congr 1
    exact (MonObj.comp_mul (CartesianMonoidalCategory.toUnit (Over.mk t)) y⁻¹ y).symm
  exact congrArg CommaMorphism.left (h2.symm.trans h1)

theorem support_zeroSchemeIdeal_pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F s, Scheme.IdealSheafData.support_comap]
  rfl

end TPSol

open TPSol in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
          (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) := by
  classical
  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := (a * b)⁻¹
  let Lp : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) → X.Modules := fun x =>
    (Scheme.Modules.pullback (T t x)).obj L
  have hLp : ∀ x, Scheme.Modules.IsInvertible (Lp x) := fun x => hL.pullback _
  let θp : ∀ x, 𝟙_ X.Modules ⟶ Lp x := fun x => Scheme.Modules.pullbackSection (T t x) θ
  let sab : 𝟙_ X.Modules ⟶ Lp a ⊗ Lp b := (λ_ (𝟙_ X.Modules)).inv ≫ (θp a ⊗ₘ θp b)
  let s₀ : 𝟙_ X.Modules ⟶ Lp c ⊗ (Lp a ⊗ Lp b) := (λ_ (𝟙_ X.Modules)).inv ≫ (θp c ⊗ₘ sab)
  have hT1 : T t (c * (a * b)) = 𝟙 X := T_inv_mul t (a * b)
  have e1 : Lp (c * (a * b)) ≅ L :=
    (Scheme.Modules.pullbackCongr hT1).app L ≪≫ (Scheme.Modules.pullbackId X).app L
  have Φ₁ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ Lp c ⊗ (Lp (a * b) ⊗ L) := whiskerLeftIso (Lp c) (hsq a b).some
  have Φ₂ : Lp c ⊗ (Lp (a * b) ⊗ L) ≅ (Lp c ⊗ Lp (a * b)) ⊗ L := (α_ (Lp c) (Lp (a * b)) L).symm
  have Φ₃ : (Lp c ⊗ Lp (a * b)) ⊗ L ≅ (Lp (c * (a * b)) ⊗ L) ⊗ L := whiskerRightIso (hsq c (a *
    b)).some L
  have Φ₄ : (Lp (c * (a * b)) ⊗ L) ⊗ L ≅ ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
    whiskerRightIso (whiskerRightIso (e1 ≪≫ (λ_ L).symm) L) L
  have Φ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ L.tensorPow 3 := Φ₁ ≪≫ Φ₂ ≪≫ Φ₃ ≪≫ Φ₄
  refine ⟨s₀ ≫ Φ.hom, ?_⟩
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]
  have hZ : Scheme.Modules.zeroSchemeIdeal s₀ =
      Scheme.Modules.zeroSchemeIdeal (θp c) *
        (Scheme.Modules.zeroSchemeIdeal (θp a) * Scheme.Modules.zeroSchemeIdeal (θp b)) := by
    rw [Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp c) ((hLp a).tensor (hLp b)),
      Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp a) (hLp b)]
  rw [hZ, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul]
  simp only [TopologicalSpace.Closeds.coe_sup]
  rw [support_zeroSchemeIdeal_pullbackSection (T t c) hL θ, support_zeroSchemeIdeal_pullbackSection
    (T t a) hL θ,
    support_zeroSchemeIdeal_pullbackSection (T t b) hL θ]
  exact Set.union_comm _ _

end translate_product
end Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
