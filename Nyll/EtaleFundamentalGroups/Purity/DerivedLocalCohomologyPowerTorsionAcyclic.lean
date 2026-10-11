/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroCoefficients
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionInjectivePresentation
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Acyclicity of ideal-power torsion coefficients

Positive-degree local cohomology vanishes on injective coefficients,
because every derived Ext group in its defining diagram vanishes.
An ideal-power torsion module over a Noetherian ring has an injective
presentation whose middle and quotient terms remain ideal-power torsion.

In degree one, the degree-zero coefficient map is surjective, so the
connecting map is both zero and an epimorphism.  In higher degrees,
induction on the quotient term and injectivity of the middle term give
the vanishing through the same connecting epimorphism.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits

variable {R : Type u} [CommRing R]

/-- Positive-degree derived local cohomology of an injective coefficient
module vanishes termwise in its defining Ext diagram. -/
theorem derivedLocalCohomology_isZero_succ_of_injective
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Injective R M] (n : ℕ) :
    IsZero (derivedLocalCohomology I M (n + 1)) := by
  let : CategoryTheory.Injective M :=
    Module.injective_object_of_injective_module R M
  apply derivedLocalCohomology_isZero_of_subsingleton_ext_powers
  intro k
  exact CategoryTheory.Abelian.Ext.subsingleton_of_injective
    (ModuleCat.of R (R ⧸ I ^ k)) M n

/-- Ideal-power torsion coefficient modules over a Noetherian ring have
zero derived local cohomology in every positive degree. -/
theorem derivedLocalCohomology_isZero_succ_of_power_torsion
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : ∀ z : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • z = 0) (n : ℕ) :
    IsZero (derivedLocalCohomology I M (n + 1)) := by
  induction n generalizing M with
  | zero =>
      obtain ⟨E, i, hi, hEinj, hE, _hQ⟩ :=
        Purity.exists_idealPowerTorsion_injective_presentation I M hM
      let : Module.Injective R E := hEinj
      let S : ShortComplex (ModuleCat.{u} R) :=
        Purity.injectivePresentationShortComplex i
      have hS : S.ShortExact :=
        Purity.injectivePresentationShortComplex_shortExact i hi
      let : Epi (derivedLocalCohomologyCoefficientsSecondMap I hS 0) :=
        derivedLocalCohomologyCoefficientsSecondMap_epi_zero_of_power_torsion I hS hE
      let : Epi (derivedLocalCohomologyCoefficientsConnectingMap I hS 0) :=
        (derivedLocalCohomologyCoefficients_afterConnecting_exact I hS 0).epi_f
          ((derivedLocalCohomology_isZero_succ_of_injective I E 0).eq_of_tgt _ _)
      have hzero : derivedLocalCohomologyCoefficientsConnectingMap I hS 0 = 0 :=
        zero_of_epi_comp (derivedLocalCohomologyCoefficientsSecondMap I hS 0)
          (derivedLocalCohomologyCoefficientsSecondMap_comp_connectingMap I hS 0)
      change IsZero (derivedLocalCohomology I S.X₁ (0 + 1))
      exact IsZero.of_epi_eq_zero
        (derivedLocalCohomologyCoefficientsConnectingMap I hS 0) hzero
  | succ n ih =>
      obtain ⟨E, i, hi, hEinj, _hE, hQ⟩ :=
        Purity.exists_idealPowerTorsion_injective_presentation I M hM
      let : Module.Injective R E := hEinj
      let S : ShortComplex (ModuleCat.{u} R) :=
        Purity.injectivePresentationShortComplex i
      have hS : S.ShortExact :=
        Purity.injectivePresentationShortComplex_shortExact i hi
      have hQzero : IsZero (derivedLocalCohomology I S.X₃ (n + 1)) :=
        ih S.X₃ hQ
      let : Epi (derivedLocalCohomologyCoefficientsConnectingMap I hS (n + 1)) :=
        (derivedLocalCohomologyCoefficients_afterConnecting_exact I hS (n + 1)).epi_f
          ((derivedLocalCohomology_isZero_succ_of_injective I E (n + 1)).eq_of_tgt _ _)
      change IsZero (derivedLocalCohomology I S.X₁ ((n + 1) + 1))
      exact IsZero.of_epi
        (derivedLocalCohomologyCoefficientsConnectingMap I hS (n + 1)) hQzero

end EtaleFundamentalGroups
