/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MonoidAlgebra.Grading
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The lattice-algebra cover and its quotient grading

For an additive subgroup `H` of a lattice `L`, the induced map of additive
monoid algebras identifies `R[H]` with the degree-zero subalgebra of `R[L]`
for the quotient grading by `L ⧸ H`.
-/

namespace EtaleFundamentalGroups.Kummer

universe u v

/--
The image of the lattice-algebra map `R[H] → R[L]` is exactly the degree-zero
subalgebra for the canonical quotient grading by `L ⧸ H`.
-/
theorem range_mapDomainAlgHom_eq_gradeZero_quotient
    {R : Type u} {L : Type v} [CommSemiring R] [AddCommGroup L]
    (H : AddSubgroup L) :
    (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype).range =
      SetLike.GradeZero.subalgebra
        (AddMonoidAlgebra.gradeBy R (QuotientAddGroup.mk' H)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ :=
      (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype).mem_range.mp hx
    change AddMonoidAlgebra.mapDomain H.subtype y ∈
      AddMonoidAlgebra.gradeBy R (QuotientAddGroup.mk' H) 0
    intro l hl
    change l ∈ (Finsupp.mapDomain H.subtype y.coeff).support at hl
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hl)
    simp
  · intro hx
    apply (AddMonoidAlgebra.mapDomainAlgHom R R H.subtype).mem_range.mpr
    refine ⟨AddMonoidAlgebra.comapDomain H.subtype H.subtype_injective x, ?_⟩
    change AddMonoidAlgebra.mapDomain H.subtype
        (AddMonoidAlgebra.comapDomain H.subtype H.subtype_injective x) = x
    apply AddMonoidAlgebra.mapDomain_comapDomain
    · intro l hl
      refine ⟨⟨l, ?_⟩, rfl⟩
      change x ∈ AddMonoidAlgebra.gradeBy R (QuotientAddGroup.mk' H) 0 at hx
      exact (QuotientAddGroup.eq_zero_iff l).mp (hx l hl)

end EtaleFundamentalGroups.Kummer
