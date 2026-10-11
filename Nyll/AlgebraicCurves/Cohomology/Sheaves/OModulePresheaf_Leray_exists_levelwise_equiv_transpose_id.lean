/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import Nyll.SchemeTheory.Cohomology.Sheaves.DoubleComplex
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex

/-! Transposition of the identity Leray double complex. -/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray

theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q
            (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q
            (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q)
          (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤
              OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by
  have h₁ : ∀ {p q : ℕ} (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
      biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ biOpen (𝟙 X) 𝒲 𝔓 p q τ σ := fun σ τ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le)
      (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  have h₂ : ∀ {p q : ℕ} (τ : 𝒲.Idx p) (σ : 𝔓.Idx q),
      biOpen (𝟙 X) 𝒲 𝔓 p q τ σ ≤ biOpen (𝟙 X) 𝔓 𝒲 q p σ τ := fun τ σ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le)
      (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  refine ⟨fun p q =>
    { toFun := fun x στ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
      map_add' := fun x y => funext fun στ => map_add _ _ _
      map_smul' := fun r x => funext fun στ => by
        change (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (r • x (στ.2, στ.1)) =
            r • (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
        exact map_smul _ _ _
      invFun := fun y τσ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₂ τσ.1 τσ.2) (y (τσ.2, τσ.1))
      left_inv := fun x => funext fun τσ => by
        change (OModulePresheaf.unit (𝟙 X ≫ π)).res _
          ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (x (τσ.1, τσ.2))) = x τσ
        exact (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).trans
          ((unit (𝟙 X ≫ π)).res_refl_apply _ _)
      right_inv := fun y => funext fun στ => by
        change (OModulePresheaf.unit (𝟙 X ≫ π)).res _
          ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (y (στ.1, στ.2))) = y στ
        exact (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).trans
          ((unit (𝟙 X ≫ π)).res_refl_apply _ _) }, ?_, ?_, ?_⟩
  · intro p q x
    change biC (𝟙 X) π 𝒲 𝔓 p q at x
    funext στ
    obtain ⟨σ, τ⟩ := στ
    change (unit (𝟙 X ≫ π)).res (h₁ σ τ) (dH (𝟙 X) π 𝒲 𝔓 p q x (τ, σ)) =
      dV (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p =>
          (unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))) (σ, τ)
    rw [dH_apply, dV_apply]
    change (unit (𝟙 X ≫ π)).res (h₁ σ τ)
        (∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (unit (𝟙 X ≫ π)).res
            (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝒲.inter_le_inter_face τ j)))
            (x (𝒲.face τ j, σ))) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (unit (𝟙 X ≫ π)).res (inf_le_inf_right _ (𝒲.inter_le_inter_face τ j))
          ((unit (𝟙 X ≫ π)).res (h₁ σ (𝒲.face τ j)) (x (𝒲.face τ j, σ)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    change (unit (𝟙 X ≫ π)).res _ ((unit (𝟙 X ≫ π)).res _ _) =
      (unit (𝟙 X ≫ π)).res _ ((unit (𝟙 X ≫ π)).res _ _)
    exact (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).trans
      (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).symm
  · intro p q x
    change biC (𝟙 X) π 𝒲 𝔓 p q at x
    funext στ
    obtain ⟨σ, τ⟩ := στ
    change (unit (𝟙 X ≫ π)).res (h₁ σ τ) (dV (𝟙 X) π 𝒲 𝔓 p q x (τ, σ)) =
      dH (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p =>
          (unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))) (σ, τ)
    rw [dV_apply, dH_apply]
    change (unit (𝟙 X ≫ π)).res (h₁ σ τ)
        (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
          (unit (𝟙 X ≫ π)).res (inf_le_inf_right _ (𝔓.inter_le_inter_face σ j))
            (x (τ, 𝔓.face σ j))) =
      ∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        (unit (𝟙 X ≫ π)).res
          (inf_le_inf_left _ (Scheme.Hom.preimage_mono (𝟙 X) (𝔓.inter_le_inter_face σ j)))
          ((unit (𝟙 X ≫ π)).res (h₁ (𝔓.face σ j) τ) (x (τ, 𝔓.face σ j)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    change (unit (𝟙 X ≫ π)).res _ ((unit (𝟙 X ≫ π)).res _ _) =
      (unit (𝟙 X ≫ π)).res _ ((unit (𝟙 X ≫ π)).res _ _)
    exact (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).trans
      (OModulePresheaf.res_res (unit (𝟙 X ≫ π)) _ _ _).symm
  · intro p q x σ τ
    rfl
end OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
