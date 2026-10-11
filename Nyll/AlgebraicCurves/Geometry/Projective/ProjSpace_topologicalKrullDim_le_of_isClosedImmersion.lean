/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_topologicalKrullDim_le_of_isClosedImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Nyll.SchemeTheory.ProjectiveSpace.Basic

/-!
# Proj Space topological Krull Dim le of is Closed Immersion
-/

section ProofImplementation


namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_topologicalKrullDim_le_of_isClosedImmersion

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DIMPROJSOL

open TopologicalSpace Order

theorem topologicalKrullDim_le_of_iSup_eq_top {X : Type u} [TopologicalSpace X] {ι : Type*}
    (U : ι → Opens X) (hU : iSup U = ⊤) (N : WithBot ℕ∞)
    (hN : ∀ i, topologicalKrullDim (U i) ≤ N) : topologicalKrullDim X ≤ N := by
  unfold topologicalKrullDim
  rw [krullDim_eq_iSup_coheight, iSup_le_iff]
  intro Z
  obtain ⟨x, hx⟩ := Z.2.nonempty
  have hxU : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hxU
  have hf : Topology.IsOpenEmbedding (Subtype.val : U i → X) := (U i).2.isOpenEmbedding_subtypeVal
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hf
  let Z' : IrreducibleCloseds (U i) := e.symm ⟨Z, ⟨⟨x, hi⟩, hx⟩⟩
  have hZ : IrreducibleCloseds.map Subtype.val hf.continuous Z' = Z :=
    congr_arg Subtype.val (e.apply_symm_apply ⟨Z, ⟨⟨x, hi⟩, hx⟩⟩)
  calc (coheight Z : WithBot ℕ∞) = coheight (IrreducibleCloseds.map Subtype.val hf.continuous Z')
    := by rw [hZ]
    _ = coheight Z' := by rw [hf.coheight_map]
    _ ≤ krullDim (IrreducibleCloseds (U i)) := coheight_le_krullDim _
    _ ≤ N := hN i

variable (k : Type u) [Field k] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

theorem ringKrullDim_away_le (i : Fin (n + 1)) :
    ringKrullDim (HomogeneousLocalization.Away 𝒜 (X i)) ≤ n := by
  classical
  let g : MvPolynomial {j : Fin (n + 1) // j ≠ i} k →ₐ[k] HomogeneousLocalization.Away 𝒜 (X i) :=
    MvPolynomial.aeval fun j => ProjSpace.ratio k n i j.1
  have hg : Function.Surjective g := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff,
      ← ProjSpace.adjoin_range_ratio k n i]
    refine Algebra.adjoin_le ?_
    intro x hx
    obtain ⟨j, rfl⟩ := hx
    by_cases hj : j = i
    · subst hj; rw [ProjSpace.ratio_self k n j]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨⟨j, hj⟩, rfl⟩
  refine (ringKrullDim_le_of_surjective g.toRingHom hg).trans ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
    ENat.card_eq_coe_fintype_card, Fintype.card_subtype_compl, Fintype.card_fin,
      Fintype.card_unique]
  simp

theorem topologicalKrullDim_basicOpen_le (i : Fin (n + 1)) :
    topologicalKrullDim (Proj.basicOpen 𝒜 (X i)) ≤ n := by
  have e := (Proj.basicOpenIsoSpec 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).hom.homeomorph
  change topologicalKrullDim (Proj.basicOpen 𝒜 (X i) : Scheme.{u}) ≤ n
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 (X i))) ≤ n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_away_le k n i

theorem iSup_basicOpen_X : (⨆ i : Fin (n + 1), Proj.basicOpen 𝒜 (X i)) = ⊤ := by
  have h1 := (ProjSpace.affineOpenCover k n).openCover.iSup_opensRange
  calc (⨆ i : Fin (n + 1), Proj.basicOpen 𝒜 (X i))
      = ⨆ i : Fin (n + 1), (Proj.awayι 𝒜 (X i) (ProjSpace.X_mem_one k n i) one_pos).opensRange :=
        iSup_congr fun i => (Proj.opensRange_awayι _ _ _ _).symm
    _ = ⊤ := h1

theorem topologicalKrullDim_proj_le : topologicalKrullDim (Proj 𝒜) ≤ n :=
  topologicalKrullDim_le_of_iSup_eq_top (fun i : Fin (n + 1) => Proj.basicOpen 𝒜 (X i))
    (iSup_basicOpen_X k n) n (topologicalKrullDim_basicOpen_le k n)

end DIMPROJSOL

open DIMPROJSOL in
theorem _root_.AlgebraicGeometry.ProjSpace.topologicalKrullDim_le_of_isClosedImmersion
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    topologicalKrullDim Z ≤ n :=
  (Topology.IsInducing.topologicalKrullDim_le ι.isClosedEmbedding.isInducing).trans
    (topologicalKrullDim_proj_le k n)
end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_topologicalKrullDim_le_of_isClosedImmersion
end ProofImplementation
