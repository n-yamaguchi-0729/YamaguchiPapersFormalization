/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension

/-!
# Mem riemann Roch Space of sum basis smul algebra Map mem map Domain
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.MemRRSpaceSumBasisSmulAlgebraMap

open AlgebraicCurve

theorem _root_.AlgebraicCurve.mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (D : Divisor K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F)
    (hmem : (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j))
      ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    ∀ j, g j ∈ LSpace (K := K) D := by
  classical
  intro j₀
  rcases eq_or_ne (g j₀) 0 with hj0 | hj0
  · rw [hj0]; exact zero_mem _
  have hj0supp : j₀ ∈ g.support := Finsupp.mem_support_iff.mpr hj0
  have hgne : g ≠ 0 := fun h => hj0 (by rw [h]; rfl)
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
  obtain ⟨hne, hle⟩ :=
    Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
      K F K' F' lift hlift_ord v B hB g hgne
  have hordSig : -(Finsupp.mapDomain lift D) (lift v) ≤
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) :=
    (mem_lSpace_iff_ord.mp hmem).resolve_left hne (lift v)
  have hmap : (Finsupp.mapDomain lift D) (lift v) = D v :=
    Finsupp.mapDomain_apply_of_injective hlift_inj D v
  rw [hmap] at hordSig
  exact hordSig.trans (hle j₀ hj0supp)
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.MemRRSpaceSumBasisSmulAlgebraMap
end ProofImplementation
