/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import SchemeTheory.ProjectiveSpace.Basic
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq
import AlgebraicCurves.Geometry.Schemes.exists_isAffineOpen_forall_mem_of_isAffineHom_proj

/-!
# Affine neighbourhoods from finite-map data

Finite-map data on a smooth proper curve gives an affine open containing prescribed
finitely many points over a fixed affine open of the base.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

with_weak_namespace _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
theorem exists_isAffineOpen_le_preimage_of_finset
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset C)
    (hF : ∀ x ∈ F, c x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ U : C.Opens, IsAffineOpen U ∧ U ≤ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ F, x
        ∈ U := by
  classical
  obtain ⟨π, h0, h1, -, -, -⟩ := 𝔉.exists_hom_proj_preimage_basicOpen_eq
  have hX : ∀ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) R) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
    fun i => ProjSpace.X_mem_one R 1 i
  have hcovP : (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
      (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R 1)
  have : IsAffineHom π := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    have hy : y ∈ (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (MvPolynomial.X i)) := by
      rw [hcovP]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ (hX i) one_pos, ?_⟩
    fin_cases i
    · simpa [h0] using 𝔉.isAffineOpen_U
    · simpa [h1] using 𝔉.isAffineOpen_V
  obtain ⟨W, hW, hFW⟩ := AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) π F
  have : IsAffine W := hW
  refine ⟨W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)), ?_, ?_, ?_⟩
  · exact (V.2.preimage (W.ι ≫ c)).image_of_isOpenImmersion W.ι
  · have : W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)) =
        W ⊓ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
          Scheme.Opens.opensRange_ι]
    rw [this]; exact inf_le_right
  · intro x hx
    refine ⟨⟨x, hFW x hx⟩, ?_, rfl⟩
    change c (W.ι ⟨x, hFW x hx⟩) ∈ (V : (Spec (CommRingCat.of R)).Opens)
    simpa using hF x hx
end SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed
  AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU
  AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway
  AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU
  AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp]
  AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq
