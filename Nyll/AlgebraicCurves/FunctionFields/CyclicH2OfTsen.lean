/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.NormSurjectiveOfTsen
import Nyll.GaloisCohomology.Kummer.FiniteCyclicUnitsH2NormSurjective

/-!
# Cyclic unit H² over curve function fields

Tsen supplies the norm preimages in the existing actual group-cohomology calculation.
This is the finite cyclic step, not a claim about all étale cohomology of a curve.
-/

namespace AlgebraicCurve

/-- Actual unit-coefficient H² vanishes for every finite cyclic Galois extension
of a one-variable function field over an algebraically closed field. -/
theorem cyclicUnitsH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] [IsCyclic Gal(E/F)]
    (c : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) : c = 0 :=
  ClassFieldTower.Cohomology.finiteCyclicUnitsH2_eq_zero_of_norm_surjective F E
    (norm_surjective_of_transcendental_of_finiteDimensional K x hx hfin hsep E) c

end AlgebraicCurve
