/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicRamificationDetection
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
import Nyll.ValuedFieldTheory.Valuation.ComapResidueCharacteristic
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Wild inertia in residue characteristic zero

An element of the actual ramification subgroup restricts to ramification at
every finite Galois layer. In residue characteristic zero those finite groups
are trivial. Every field element belongs to a finite Galois layer, so the
original automorphism is the identity.

This supplies the residue-characteristic-zero wild-inertia assertion of
Stacks Project Tag 0BUA for valuation subrings, including infinite extensions.
It does not require Henselianity, discreteness, or a perfect residue field.
-/

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Wild inertia is trivial in residue characteristic zero for a possibly
infinite Galois extension and any chosen valuation subring upstairs. -/
theorem ramificationGroup_eq_bot_of_isGalois_residueCharZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (A : ValuationSubring L) [CharZero (IsLocalRing.ResidueField A)] :
    ramificationGroup K A = ⊥ := by
  apply bot_unique
  intro σ hσ
  change σ = 1
  apply Subtype.ext
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  let E : FiniteGaloisIntermediateField K L :=
    FiniteGaloisIntermediateField.adjoin K {x}
  have hx : x ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)
  let B : ValuationSubring E := A.comap E.toIntermediateField.val.toRingHom
  have : CharZero (IsLocalRing.ResidueField B) :=
    ValuationSubring.charZero_residueField_comap A E.toIntermediateField.val.toRingHom
  obtain ⟨τ, hτ, hτσ⟩ :=
    (mem_ramificationGroup_iff_forall_finiteGalois_restrict K A σ).mp hσ E
  have hτone : τ = 1 := by
    have hB := ramificationGroup_eq_bot_of_residueCharZero K B
    rw [hB] at hτ
    exact hτ
  have hrestrict :
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
        (inertiaGroupToAut (K := K) A σ) = 1 := by
    rw [← hτσ, hτone, map_one]
  have hcomm := AlgEquiv.restrictNormal_commutes
    (inertiaGroupToAut (K := K) A σ) E (⟨x, hx⟩ : E)
  rw [show (inertiaGroupToAut (K := K) A σ).restrictNormal E = 1 from hrestrict] at hcomm
  exact hcomm.symm

end EtaleFundamentalGroups.Inertia
