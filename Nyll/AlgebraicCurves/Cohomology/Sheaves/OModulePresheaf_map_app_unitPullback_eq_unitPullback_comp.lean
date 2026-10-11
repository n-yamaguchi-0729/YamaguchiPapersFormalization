/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback

/-!
# OModule Presheaf map app unit Pullback eq unit Pullback comp
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

theorem _root_.AlgebraicGeometry.OModulePresheaf.map_app_unitPullback_eq_unitPullback_comp
    {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R''] {X X' Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πX' : X' ⟶ Spec (CommRingCat.of R'')) (πY : Y ⟶ Spec
      (CommRingCat.of R))
    (h : X ⟶ Y) (g : X' ⟶ X) [IsAffineHom g]
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (hlam' : ∀ w : (𝒲.comap g).ι, (𝒲.comap g).U w ≤ (g ≫ h) ⁻¹ᵁ 𝒦.U (lam w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (s : (𝒲.comap g).Idx n) :
    (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom
        ((g.app (𝒲.inter s)).hom (OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z s))
      = OModulePresheaf.unitPullback (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n z s := by
  classical
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n z s hinj,
      OModulePresheaf.unitPullback_apply_of_injective (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam hlam' n
        z s hinj,
      map_zsmul, map_zsmul]
    congr 1
    have key : h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫
        X.presheaf.map (homOfLE (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).op ≫
          g.app (𝒲.inter s) ≫ X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op =
        h.app (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫ g.app (h ⁻¹ᵁ 𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) ≫
          X'.presheaf.map (homOfLE ((𝒲.comap g).inter_le_preimage_inter_sortIdx (g ≫ h) 𝒦 lam hlam'
            s hinj)).op := by
      congr 1
      rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
      rfl
    have e := congrArg (fun φ => φ.hom (z (𝒲.sortIdx 𝒦 lam s hinj))) key
    simp only [CommRingCat.hom_comp] at e
    exact e
  · rw [OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n z s hinj,
      OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX') (g ≫ h) (𝒲.comap g) 𝒦 lam
        hlam' n z s hinj]
    change (X'.presheaf.map (homOfLE (𝒲.comap_inter_le g s)).op).hom ((g.app (𝒲.inter s)).hom (0 :
      Γ(X, 𝒲.inter s))) =
      (0 : Γ(X', (𝒲.comap g).inter s))
    rw [map_zero, map_zero]
end OModulePresheaf_map_app_unitPullback_eq_unitPullback_comp
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
