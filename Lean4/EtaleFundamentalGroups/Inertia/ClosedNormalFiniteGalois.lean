/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Closed normal subgroups detected by finite Galois subfields

Every element of the fixed field of a closed normal subgroup lies in a
finite Galois subfield of that same fixed field. Thus the subgroup is the
intersection of the finite Galois restriction kernels containing it.
This gives the field-theoretic finite-quotient criterion needed in Tag 0BTD.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L]
  [Algebra K L] [IsGalois K L]

/-- A closed normal Galois subgroup is detected by the finite Galois
subextensions which it fixes. The finite subextension containing a specified
fixed element is constructed by taking its actual normal closure. -/
theorem closedNormalSubgroup_eq_iInf_finiteGalois_fixingSubgroup
    (H : ClosedSubgroup Gal(L/K)) [H.toSubgroup.Normal] :
    H.toSubgroup =
      ⨅ (E : FiniteGaloisIntermediateField K L)
        (_ : H.toSubgroup ≤ E.toIntermediateField.fixingSubgroup),
        E.toIntermediateField.fixingSubgroup := by
  apply le_antisymm
  · apply le_iInf
    intro E
    apply le_iInf
    intro hE
    exact hE
  · intro σ hσ
    rw [← InfiniteGalois.fixingSubgroup_fixedField H]
    apply (IntermediateField.mem_fixingSubgroup_iff
      (IntermediateField.fixedField H.toSubgroup) σ).mpr
    intro x hx
    let E := FiniteGaloisIntermediateField.adjoin K ({x} : Set L)
    have hE : E.toIntermediateField ≤ IntermediateField.fixedField H.toSubgroup := by
      change IntermediateField.normalClosure K
        (IntermediateField.adjoin K ({x} : Set L)) L ≤
          IntermediateField.fixedField H.toSubgroup
      exact IntermediateField.normalClosure_le_iff_of_normal.mpr
        (IntermediateField.adjoin_simple_le_iff.mpr hx)
    have hfix : H.toSubgroup ≤ E.toIntermediateField.fixingSubgroup :=
      (IntermediateField.le_iff_le H.toSubgroup E.toIntermediateField).mp hE
    have hσE : σ ∈ E.toIntermediateField.fixingSubgroup :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ E) hfix
    exact (IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField σ).mp hσE
      x (FiniteGaloisIntermediateField.subset_adjoin K ({x} : Set L)
        (Set.mem_singleton x))

/-- Closed normal generation in a Galois group can be tested using the
actual restrictions to finite Galois intermediate fields. -/
theorem topologicalClosure_normalClosure_eq_iInf_finiteGalois
    (s : Set Gal(L/K)) :
    (Subgroup.normalClosure s).topologicalClosure =
      ⨅ (E : FiniteGaloisIntermediateField K L)
        (_ : s ⊆ (E.toIntermediateField.fixingSubgroup : Set Gal(L/K))),
        E.toIntermediateField.fixingSubgroup := by
  apply le_antisymm
  · apply le_iInf
    intro E
    apply le_iInf
    intro hs
    exact Subgroup.topologicalClosure_minimal (Subgroup.normalClosure s)
      (Subgroup.normalClosure_le_normal hs)
      (InfiniteGalois.fixingSubgroup_isClosed E.toIntermediateField)
  · let H : ClosedSubgroup Gal(L/K) :=
      ⟨(Subgroup.normalClosure s).topologicalClosure,
        Subgroup.isClosed_topologicalClosure (Subgroup.normalClosure s)⟩
    have : H.toSubgroup.Normal :=
      Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure s)
    change (⨅ (E : FiniteGaloisIntermediateField K L)
      (_ : s ⊆ (E.toIntermediateField.fixingSubgroup : Set Gal(L/K))),
        E.toIntermediateField.fixingSubgroup) ≤ H.toSubgroup
    rw [closedNormalSubgroup_eq_iInf_finiteGalois_fixingSubgroup K L H]
    apply le_iInf
    intro E
    apply le_iInf
    intro hE σ hσ
    have hs : s ⊆ (E.toIntermediateField.fixingSubgroup : Set Gal(L/K)) := by
      intro τ hτ
      exact hE (Subgroup.le_topologicalClosure (Subgroup.normalClosure s)
        (Subgroup.subset_normalClosure hτ))
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hσ E) hs

end EtaleFundamentalGroups.Inertia
