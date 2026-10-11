/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification degree with trivial residue extension

For a finite local extension of discrete valuation rings, a bijection on
residue fields forces the inertia degree to be one.  The local Dedekind
identity `e * f = [L : K]` then identifies the ramification index with the
degree of the fraction-field extension.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uK uL

/-- A finite local extension of DVRs inducing an isomorphism on residue
fields has ramification index equal to its generic degree. -/
theorem maximalIdeal_ramificationIdx_eq_finrank_of_residueFieldMap_bijective
    {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S]
    (hres : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R S))) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R =
      Module.finrank K L := by
  let : FaithfulSMul R S :=
    FaithfulSMul.of_field_isFractionRing R S K L
  have hres' : Function.Bijective
      (algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S)) := by
    have hmap :
        IsLocalRing.ResidueField.map (algebraMap R S) =
          algebraMap (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField S) := by
      ext x
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rfl
    rw [← hmap]
    exact hres
  have hinertia :
      (IsLocalRing.maximalIdeal S).inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal
      (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)]
    exact Module.finrank_of_bijective_algebraMap hres'
  have hp : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField R)
  have hfundamental :=
    Ideal.sum_ramification_inertia_eq_finrank
      (IsLocalRing.maximalIdeal R) S
  let : Unique ((IsLocalRing.maximalIdeal R).primesOver S) :=
    { default := ⟨IsLocalRing.maximalIdeal S, by
          rw [IsLocalRing.primesOver_eq S hp]
          simp⟩
      uniq := fun q ↦ Subtype.ext (by
        have hq : (q : Ideal S) ∈ (IsLocalRing.maximalIdeal R).primesOver S := q.property
        simpa only [IsLocalRing.primesOver_eq S hp,
          Set.mem_singleton_iff] using hq) }
  rw [Fintype.sum_unique] at hfundamental
  change (IsLocalRing.maximalIdeal S).ramificationIdx R *
    (IsLocalRing.maximalIdeal S).inertiaDeg R = Module.finrank R S at hfundamental
  rw [hinertia, mul_one] at hfundamental
  simpa only [IsFractionRing.finrank_eq R K S L] using hfundamental

end EtaleFundamentalGroups

end
