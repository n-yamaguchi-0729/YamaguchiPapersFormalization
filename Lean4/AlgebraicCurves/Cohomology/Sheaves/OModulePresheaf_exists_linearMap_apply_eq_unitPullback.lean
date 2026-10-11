/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_linearMap_apply_eq_unitPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback

/-!
# OModule Presheaf exists linear Map apply eq unit Pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_exists_linearMap_apply_eq_unitPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_linearMap_apply_eq_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    ∃ L : (OModulePresheaf.unit πY).cochain 𝒦 n →ₗ[R] (OModulePresheaf.unit πX).cochain 𝒲 n,
      ∀ z, L z = OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  subst hh
  refine ⟨{ toFun := fun z => OModulePresheaf.unitPullback (πX := h ≫ πY) h 𝒲 𝒦 lam hlam n z
            map_add' := ?_
            map_smul' := ?_ }, fun z => rfl⟩
  · intro z₁ z₂
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      erw [map_add, map_add, smul_add]
      try rfl
    · rw [Pi.add_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, add_zero]
  · intro r z
    funext s
    by_cases hinj : Function.Injective (lam ∘ s.1)
    · rw [Pi.smul_apply, RingHom.id_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _
        _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
      let i1 := Scheme.TwoAffineOpenCover.algebraOfHom πY (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))
      let i2 := Scheme.TwoAffineOpenCover.algebraOfHom (h ≫ πY) (𝒲.inter s)
      change (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) • (X.presheaf.map (homOfLE
        (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom ((h.app (𝒦.inter
        (𝒲.sortIdx 𝒦 lam s hinj))).hom (algebraMap R Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) r *
        (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj)))) =
        algebraMap R Γ(X, 𝒲.inter s) r * ((((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ)) •
          (X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op).hom
          ((h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj))).hom (show Γ(Y, 𝒦.inter (𝒲.sortIdx 𝒦 lam s
          hinj)) from z (𝒲.sortIdx 𝒦 lam s hinj))))
      rw [map_mul, map_mul, zsmul_eq_mul, zsmul_eq_mul, mul_left_comm]
      congr 1
      have hYTop : 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj) ≤ πY ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by
        rw [Scheme.Hom.preimage_top]
        exact le_top
      have hXTop : 𝒲.inter s ≤ (h ≫ πY) ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by
        rw [Scheme.Hom.preimage_top]
        exact le_top
      change ((πY.appLE ⊤ (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) hYTop ≫ h.appLE (𝒦.inter (𝒲.sortIdx 𝒦
        lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj))).hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
        ((h ≫ πY).appLE ⊤ (𝒲.inter s) hXTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [Scheme.Hom.appLE_comp_appLE]
    · rw [Pi.smul_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj,
        OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, smul_zero]
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_exists_linearMap_apply_eq_unitPullback
end ProofImplementation
