/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.FieldTheory.FiniteAlgebraicConstants
import Nyll.GaloisCohomology.FieldTheory.IntegralClosureTorsion
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteNormCompleteExtension
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.TorsionFiniteness
import Nyll.ValuedFieldTheory.Valuation.FiniteResidueExtension

/-!
# Roots of unity in finitely generated p-adic extensions

Finite extensions of the p-adic field have finite torsion unit groups.
The same finiteness holds in essentially finite-type extensions by
passing to their finite extension of algebraic constants.
-/

namespace Yamaguchi26AbfaithfulGalois
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
universe u

theorem padicCompleteDVF_residue_char (p : ℕ) [Fact p.Prime] :
    CharP (padicCompleteDVF p).residueField p := by
  let e := (IsLocalRing.ResidueField.mapEquiv (padicIntEquivValuationSubring p)).symm.trans
    (padicIntResidueFieldEquivZMod p)
  exact charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p

/-- Finite extensions of Q_p have finite torsion units, via their actual residue field. -/
theorem finite_torsion_finiteExtension_padic
    (p : ℕ) [Fact p.Prime] (C : Type u) [Field C] [Algebra (Padic p) C]
    [FiniteDimensional (Padic p) C] : Finite (CommGroup.torsion Cˣ) := by
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (Padic p) C).injective
  let base := padicCompleteDVF p
  let D := base.finiteExtension C
  have : base.valuation.HasExtension D.valuation := base.finiteExtension_hasExtension C
  have : Finite base.residueField := padicCompleteDVF_residueField_finite p
  have : CharP base.residueField p := padicCompleteDVF_residue_char p
  have : FiniteDimensional base.residueField D.residueField :=
    Valuation.finiteDimensional_residueField base.valuation D.valuation
  have : Finite D.residueField := Module.finite_of_finite base.residueField
  have : CharP D.residueField p := charP_of_injective_algebraMap
    (algebraMap base.residueField D.residueField).injective p
  exact D.toDVF.finite_torsion_of_finite_residueTorsion_mixedChar p

/-- Roots of unity in a finitely generated Q_p-extension lie in its finite
extension of algebraic constants. -/
theorem finite_torsion_of_essFiniteType_padic
    (p : ℕ) [Fact p.Prime] (E : Type u) [Field E] [Algebra (Padic p) E]
    [Algebra.EssFiniteType (Padic p) E] : Finite (CommGroup.torsion Eˣ) := by
  let C := algebraicClosure (Padic p) E
  have : Module.Finite (Padic p) C := FieldTheory.finite_algebraic_subextension (Padic p) C E
  have : Finite (CommGroup.torsion Cˣ) := finite_torsion_finiteExtension_padic p C
  have : Finite (CommGroup.torsion (integralClosure (Padic p) E)ˣ) :=
    inferInstanceAs (Finite (CommGroup.torsion Cˣ))
  exact Finite.of_injective (FieldTheory.torsionUnitsIntegralClosureEquiv (Padic p) E)
    (FieldTheory.torsionUnitsIntegralClosureEquiv (Padic p) E).injective

end Yamaguchi26AbfaithfulGalois
