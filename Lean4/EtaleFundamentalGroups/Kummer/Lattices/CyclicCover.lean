/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import EtaleFundamentalGroups.Kummer.Lattices.Cover

/-!
# Cyclic quotient coordinates for a finite-index lattice cover

A finite quotient lattice admits cyclic coordinates.  Composing those
coordinates with the quotient map gives a grading of the ambient lattice
algebra whose degree-zero subalgebra is the original lattice algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u v

/--
For a finite-index additive subgroup `H ≤ L`, choose cyclic coordinates on
`L ⧸ H`.  In those coordinates, the image of `R[H] → R[L]` remains exactly
the degree-zero subalgebra.
-/
theorem exists_cyclicQuotientGrading_range_eq_gradeZero
    {R : Type u} {L : Type v} [CommSemiring R] [AddCommGroup L]
    (H : AddSubgroup L) [Finite (L ⧸ H)] :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧
        ∃ e : (L ⧸ H) ≃+ (∀ i, ZMod (n i)),
          (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype).range =
            SetLike.GradeZero.subalgebra
              (AddMonoidAlgebra.gradeBy R
                (e.toAddMonoidHom.comp (QuotientAddGroup.mk' H))) := by
  obtain ⟨ι, hι, n, hn, ⟨eDirectSum⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite' (L ⧸ H)
  let : Fintype ι := hι
  let e : (L ⧸ H) ≃+ (∀ i, ZMod (n i)) :=
    eDirectSum.trans (DirectSum.addEquivProd _)
  refine ⟨ι, inferInstance, n, hn, e, ?_⟩
  rw [range_mapDomainAlgHom_eq_gradeZero_quotient H]
  ext x
  change
    (x ∈ AddMonoidAlgebra.gradeBy R (QuotientAddGroup.mk' H) 0) ↔
      x ∈ AddMonoidAlgebra.gradeBy R
        (e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)) 0
  constructor
  · intro hx l hl
    change e (QuotientAddGroup.mk' H l) = 0
    rw [hx l hl, map_zero]
  · intro hx l hl
    apply e.injective
    have hxl := hx l hl
    change e (QuotientAddGroup.mk' H l) = 0 at hxl
    simpa only [map_zero] using hxl

end EtaleFundamentalGroups.Kummer
