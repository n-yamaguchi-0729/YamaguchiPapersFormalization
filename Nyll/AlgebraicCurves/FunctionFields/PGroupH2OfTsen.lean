/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.NormSurjectiveOfTsen
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormSurjective
import Nyll.GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2
import Nyll.GaloisCohomology.GroupTheory.PGroupGaloisTower
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Unit H² of finite Galois p-extensions of curve function fields

A central prime-order subgroup supplies an actual intermediate field.
Tsen kills the cyclic upper extension, induction kills the lower extension,
and the existing unit H² inflation-restriction exactness kills the original class.
-/

open CategoryTheory

namespace AlgebraicCurve

/-- Actual unit-coefficient H² vanishes for finite Galois p-extensions of
one-variable function fields over algebraically closed fields. -/
theorem pGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hP : IsPGroup p Gal(E/F))
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) : c = 0 := by
  generalize hn : Module.finrank F E = n
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    rcases subsingleton_or_nontrivial Gal(E/F) with hTrivial | hNontrivial
    · have : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) :=
        ModuleCat.isZero_iff_subsingleton.mp
          (isZero_groupCohomology_succ_of_subsingleton
            (Rep.ofAlgebraAutOnUnits F E) 1)
      exact Subsingleton.elim _ _
    · obtain ⟨L, hBase, hTop, hBaseP, hCyclic, _, hSmaller, _⟩ :=
        IsGalois.exists_intermediateField_prime_degree_of_isPGroup F E p hP
      let : Algebra K L :=
        ((algebraMap F L).comp (algebraMap K F)).toAlgebra
      have : IsScalarTower K F L :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hUpper :
          (ClassFieldTower.Cohomology.finiteGaloisTowerUnitsH2Restriction F L E).hom c = 0 :=
        ClassFieldTower.Cohomology.finiteCyclicUnitsH2_eq_zero_of_norm_surjective L E
          (norm_surjective_over_finite_extension K x hx hfin L E) _
      obtain ⟨b, hb⟩ :=
        ClassFieldTower.Cohomology.finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range
          F L E hUpper
      have hb0 : b = 0 :=
        ih (Module.finrank F L) (hn ▸ hSmaller) L hBaseP b rfl
      rw [← hb, hb0, map_zero]

end AlgebraicCurve
