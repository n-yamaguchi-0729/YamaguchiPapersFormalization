/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_adeleSpaceQuot_H1.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.Mem_adeleSpace_iff_mem_repartitions
import Nyll.AlgebraicCurves.Cohomology.Mem_repartitionsOf_iff_coe_mem_adeleBdd
import Nyll.AlgebraicCurves.Cohomology.Mem_principalRepartitions_iff_coe_mem_globalSub

/-!
# Exists linear Equiv adele Space Quot H1
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Exists_linearEquiv_adeleSpaceQuot_H1

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_linearEquiv_adeleSpaceQuot_H1 {K F : Type*} [Field K] [Field
  F] [Algebra K F]
    [HasPrincipalDivisors K F] (D : Divisor K F) :
    ∃ e : (↥(adeleSpace K F) ⧸ adeleBddPrincipal K F D) ≃ₗ[K] H1 D,
      ∀ (a : ↥(adeleSpace K F)) (ha : (a : Place K F → F) ∈ repartitions K F),
        e (Submodule.Quotient.mk a) = Submodule.Quotient.mk ⟨(a : Place K F → F), ha⟩ := by
  let ι : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F) :=
    { toFun := fun a => ⟨(a : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mp a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let N : Submodule K ↥(repartitions K F) := repartitionsOf D ⊔ principalRepartitions K F
  let φ : ↥(adeleSpace K F) →ₗ[K] H1 D := N.mkQ ∘ₗ ι
  have hker : LinearMap.ker φ = adeleBddPrincipal K F D := by
    apply le_antisymm
    · intro a ha
      rw [LinearMap.mem_ker] at ha
      change Submodule.Quotient.mk (ι a) = 0 at ha
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_sup] at ha
      obtain ⟨r, hr, p, hp, hrp⟩ := ha
      have hr' : ((⟨(r : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr r.2⟩ :
          ↥(adeleSpace K F))) ∈ (adeleBdd D).comap (adeleSpace K F).subtype :=
        mem_repartitionsOf_iff_coe_mem_adeleBdd.mp hr
      have hp' : ((⟨(p : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr p.2⟩ :
          ↥(adeleSpace K F))) ∈ (globalSub K F).comap (adeleSpace K F).subtype :=
        mem_principalRepartitions_iff_coe_mem_globalSub.mp hp
      have hsum : a = ⟨(r : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr r.2⟩
          + ⟨(p : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr p.2⟩ := by
        apply Subtype.ext
        exact (congrArg (fun x : ↥(repartitions K F) => (x : Place K F → F)) hrp).symm
      rw [hsum]
      exact Submodule.add_mem_sup hr' hp'
    · refine sup_le ?_ ?_
      · intro a ha
        rw [LinearMap.mem_ker]
        change Submodule.Quotient.mk (ι a) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_left (mem_repartitionsOf_iff_coe_mem_adeleBdd.mpr ha)
      · intro a ha
        rw [LinearMap.mem_ker]
        change Submodule.Quotient.mk (ι a) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.mem_sup_right (mem_principalRepartitions_iff_coe_mem_globalSub.mpr ha)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨⟨(β : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr β.2⟩, rfl⟩
  have hle : adeleBddPrincipal K F D ≤ LinearMap.ker φ := hker.ge
  refine ⟨LinearEquiv.ofBijective ((adeleBddPrincipal K F D).liftQ φ hle) ⟨?_, ?_⟩, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  · intro q
    obtain ⟨a, rfl⟩ := hφ q
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  · intro a ha
    rfl
end AlgebraicCurves.Cohomology.Proofs.Exists_linearEquiv_adeleSpaceQuot_H1
end ProofImplementation
