/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactorFiniteEtale
import EtaleFundamentalGroups.StrictHenselian.ChosenFactorFilteredDescent

/-!
# Finite-stage descent of the retained lower-radical unit factor

The literal factor retained by `HigherRadicalUnitFactorData` is finite etale
over the actual ramification-index radical.  If it has a unique closed prime
after passage to a strictly Henselian filtered colimit, finite presentation
therefore descends its trivialization to one finite stage of the same system.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u w x

local instance underCommRingCatAlgebraHigherRadicalFilteredDescent
    {R : Type u} [CommRing R]
    (A : Under (CommRingCat.of R)) : Algebra R A :=
  RingHom.toAlgebra A.hom.hom

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable (base : DVF.{u, w} K) (target : DVF.{u, x} L)
variable [base.valuation.HasExtension target.valuation]
variable [Module.Finite base.valuationSubring target.valuationSubring]
variable (varpi : base.valuationSubring)
variable (pi : target.valuationSubring) (N : ℕ)
variable (beta : AlgebraicClosure L)
variable (factor : HigherRadicalUnitFactorData
  base target varpi pi N beta)

local notation "Rₑ" => AdjoinRoot
  (X ^ ramificationIndex base target - C varpi)
local notation "Cq" => AdjoinRoot factor.q

local instance higherRadicalUnitFactorFilteredDescentAlgebra :
    Algebra Rₑ Cq :=
  factor.radicalToUnitFactor.toRingHom.toAlgebra

/-- The retained unit factor becomes the base at one finite stage of any
strict-Henselian filtered system in which its closed prime is unique.

The finite-etale and module-finite hypotheses are supplied internally by
`factor.radical_etale` and
`higherRadicalUnitFactorData_radical_finite`.  Noetherianity of the lower
radical supplies the finite-presentation input required by descent. -/
theorem
    exists_higherRadicalUnitFactor_trivial_stage_of_filteredColimit
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : CategoryTheory.Functor J (Under (CommRingCat.of Rₑ)))
    (c : Cocone F) (hc : IsColimit c)
    [HenselianLocalRing c.pt]
    [IsSepClosed (IsLocalRing.ResidueField c.pt)]
    (q : Ideal (c.pt ⊗[Rₑ] Cq)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal c.pt)]
    (hunique : ∀ Q : Ideal (c.pt ⊗[Rₑ] Cq), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal c.pt) → Q = q) :
    ∃ (i : J), Nonempty
      ((F.obj i ⊗[Rₑ] Cq) ≃ₐ[F.obj i] F.obj i) := by
  let V := base.valuationSubring
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : Algebra.Etale Rₑ Cq := factor.radical_etale
  let : Module.Finite Rₑ Cq :=
    higherRadicalUnitFactorData_radical_finite
      base target varpi pi N beta factor
  let : Module.Finite V Rₑ :=
    (monic_X_pow_sub_C varpi
      (ramificationIndex_pos_of_moduleFinite base target).ne').finite_adjoinRoot
  let : IsNoetherianRing Rₑ := IsNoetherianRing.of_finite V Rₑ
  exact
    exists_strictHenselianChosenFactor_trivial_stage_of_filteredColimit_of_noetherian
      F c hc q hunique

end

end EtaleFundamentalGroups.Kummer

end
