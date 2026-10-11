/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.Compactness.Compact

/-!
# Scheme is Clopen preimage sigma Inj and exists Unique lift of hom sigma
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace CoprodPtsA

variable {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H)

theorem range_sigmaι_eq (i : σ) :
    Set.range (Sigma.ι H i).base = sigmaMk H '' Set.range (Sigma.mk i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨i, x⟩, ⟨x, rfl⟩, sigmaMk_mk H i x⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (sigmaMk_mk H i x).symm⟩

theorem isClosed_opensRange (i : σ) : IsClosed ((Sigma.ι H i).opensRange : Set ↥(∐ H)) := by
  rw [Scheme.Hom.coe_opensRange, range_sigmaι_eq]
  exact (sigmaMk H).isClosed_image.mpr isClosed_range_sigmaMk

theorem iSup_opensRange : (⨆ i, (Sigma.ι H i).opensRange) = ⊤ := by
  exact (sigmaOpenCover H).iSup_opensRange




theorem closed (i : σ) : IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) :=
  (isClosed_opensRange H i).preimage u.continuous

theorem disjoint (i j : σ) (hij : i ≠ j) :
    Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange) :=
  Opens.coe_disjoint.mp ((Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι H i j hij)).preimage
    u.base)

theorem cover : (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_opensRange, Scheme.Hom.preimage_top]

theorem range_subset (i : σ) :
    Set.range ((u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u).base ⊆ Set.range (Sigma.ι H i).base := by
  rintro _ ⟨x, rfl⟩
  have hx : (x.1 : T) ∈ (u ⁻¹ᵁ (Sigma.ι H i).opensRange : Set T) := x.2
  have hx' : u.base x.1 ∈ Set.range (Sigma.ι H i).base := by
    rw [← Scheme.Hom.coe_opensRange]; exact hx
  change u.base x.1 ∈ Set.range (Sigma.ι H i).base
  exact hx'

theorem lift (i : σ) : ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u := by
  refine ⟨IsOpenImmersion.lift (Sigma.ι H i) _ (range_subset H u i), IsOpenImmersion.lift_fac _ _
    _, fun v hv => ?_⟩
  rw [← cancel_mono (Sigma.ι H i), hv, IsOpenImmersion.lift_fac]




theorem finite [CompactSpace T] :
    {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) (fun i => (u ⁻¹ᵁ _).isOpen)
    (by
      intro x _
      have hx : x ∈ ((⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) :=
        by rw [cover]; trivial
      simpa [Opens.coe_iSup] using hx)
  refine t.finite_toSet.subset ?_
  rintro j ⟨x, hx⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) := by
    simpa using ht (Set.mem_univ x)
  by_cases hij : i = j
  · exact hij ▸ hi
  · exact ((Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (disjoint H u i j hij))) ⟨hxi, hx⟩).elim

end CoprodPtsA

theorem
  _root_.AlgebraicGeometry.Scheme.isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
    {σ : Type u} (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    (∀ i, IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) ∧
    (∀ i j, i ≠ j → Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange)) ∧
    (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ ∧
    (∀ i, ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u) ∧
    (CompactSpace T → {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set
      T).Nonempty}.Finite) :=
  ⟨CoprodPtsA.closed H u, CoprodPtsA.disjoint H u, CoprodPtsA.cover H u, CoprodPtsA.lift H u,
    fun _ => CoprodPtsA.finite H u⟩
end Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
