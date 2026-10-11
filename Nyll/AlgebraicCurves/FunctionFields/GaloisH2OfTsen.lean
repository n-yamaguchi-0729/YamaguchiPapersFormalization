/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.PGroupH2OfTsen
import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace
import Nyll.GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport

/-!
# Unit H² of arbitrary finite Galois extensions of curve function fields

The Sylow fixed fields remain one-variable function fields. Their relative Galois
groups are p-groups, so the previously proved vanishing applies. The finite-index
trace detects vanishing in the original actual group-cohomology object.
-/

open CategoryTheory

namespace AlgebraicCurve

/-- Actual unit H² vanishes for every finite Galois extension of a one-variable
function field over an algebraically closed field. -/
theorem galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) : c = 0 := by
  apply ClassFieldTower.Cohomology.H2_eq_zero_of_sylow_restrictions_isZero
    (Rep.ofAlgebraAutOnUnits F E) ?_ c
  intro p hp P
  let L : IntermediateField F E := IntermediateField.fixedField (P : Subgroup Gal(E/F))
  let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsGalois L E := IsGalois.of_fixed_field E (P : Subgroup Gal(E/F))
  have hP : IsPGroup p Gal(E/L) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv
      (P : Subgroup Gal(E/F)))
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin L
  have hz (a : groupCohomology (Rep.ofAlgebraAutOnUnits L E) 2) : a = 0 :=
    pGroupUnitsH2_eq_zero_of_transcendental_of_finiteDimensional K y hy hyfin p E hP a
  let : Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits L E) 2) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  have hzero : Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits L E) 2) :=
    ModuleCat.isZero_of_subsingleton _
  have heq : L.fixingSubgroup = (P : Subgroup Gal(E/F)) :=
    IntermediateField.fixingSubgroup_fixedField (P : Subgroup Gal(E/F))
  change Limits.IsZero (groupCohomology
    (Rep.res (P : Subgroup Gal(E/F)).subtype (Rep.ofAlgebraAutOnUnits F E)) 2)
  rw [← heq]
  exact hzero.of_iso
    (ClassFieldTower.Cohomology.finiteGaloisUnitsRelativeCohomologyIso F E L 2)

end AlgebraicCurve
