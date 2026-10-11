/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CechLocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.CechLocalizationComplex
import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalCohomologyDualSupportDimension
import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalSaturatedPowers
import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalTopCohomologyDual
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyFiniteTorsionFreeDescent
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleRadical
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionFreeTopMultiplication
import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionFunctor
import Nyll.EtaleFundamentalGroups.Purity.InjectiveChainLocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.InjectiveLinearDualHomology
import Nyll.EtaleFundamentalGroups.Purity.ModuleInjectiveHull
import Nyll.EtaleFundamentalGroups.Purity.SaturatedPowerDegreeZeroLocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.TensorDualComplexTorsionLifting
import Nyll.EtaleFundamentalGroups.Purity.TensorLinearDualComplex
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Hartshorne--Lichtenbaum vanishing over a complete local domain

A parameter Čech complex gives a bounded flat model for maximal-support
local cohomology. Its dual into the residue-field injective hull is a
bounded complex of injectives. Saturated powers remove degree-zero
maximal-support cohomology while remaining cofinal with powers of the
support ideal, which gives the required surjectivity on torsion.

A common nonzero annihilator of the lower dual cohomology propagates to
the top cycle module. That module is finite, nonzero, and torsion-free.
Surjectivity of nonzero scalar multiplication on its top local cohomology
then forces vanishing, which descends from the cycle module to the ring.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing MonoidalCategory

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- The unit comparison is made on complexes before taking homology. -/
private def tensorRingComplexIso
    (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft (ModuleCat.of R R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C ≅ C :=
  HomologicalComplex.Hom.isoOfComponents (fun n => λ_ (C.X n))
    (fun i j _ => (leftUnitor_naturality (C.d i j)).symm)

/-- The parameter Čech comparison retains its linear coefficient module. -/
private def cechMaximalLocalCohomologyLinearEquiv
    [IsNoetherianRing R] [IsLocalRing R]
    (xs : List R) (hrad : (Ideal.ofList xs).radical = maximalIdeal R)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ((((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cechLocalizationComplex xs)).homology n) ≃ₗ[R]
        derivedLocalCohomologyModule (maximalIdeal R) M n :=
  (cechLocalCohomologyLinearEquiv xs M n).trans
    (derivedLocalCohomologyModuleLinearEquivOfSameRadical
      (hrad.trans (maximalIdeal.isMaximal R).isPrime.radical.symm) M n)

/-- The same comparison for the underlying parameter Čech complex. -/
private def cechRingMaximalLocalCohomologyLinearEquiv
    [IsNoetherianRing R] [IsLocalRing R]
    (xs : List R) (hrad : (Ideal.ofList xs).radical = maximalIdeal R) (n : ℕ) :
    (cechLocalizationComplex xs).homology n ≃ₗ[R]
      derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (tensorRingComplexIso (cechLocalizationComplex xs)).symm).toLinearEquiv.trans
      (cechMaximalLocalCohomologyLinearEquiv xs hrad (ModuleCat.of R R) n)

/-- Top local cohomology of a complete Noetherian local domain vanishes
for every proper support ideal whose radical is not the maximal ideal. -/
theorem derivedLocalCohomology_isZero_of_completeLocalDomain_of_radical_ne
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≠ ⊤) (hIradical : I.radical ≠ maximalIdeal R)
    (d : ℕ) (hdim : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    IsZero (derivedLocalCohomology I (ModuleCat.of R R) (d + 1)) := by
  obtain ⟨E, i, hi, hess, hEinj⟩ :=
    exists_module_injective_hull (ModuleCat.of R (R ⧸ maximalIdeal R))
  let : Module.Injective R E := hEinj
  obtain ⟨xs, hlen, hrad⟩ :=
    exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq (d + 1) hdim
  let C : CochainComplex (ModuleCat.{u} R) ℕ := cechLocalizationComplex xs
  let D : ChainComplex (ModuleCat.{u} R) ℕ := linearDualComplex E C
  let eH (n : ℕ) : D.homology n ≃ₗ[R]
      (derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) n →ₗ[R] E) :=
    (injectiveLinearDualComplexHomologyIso E C n).toLinearEquiv.trans
      (LinearEquiv.arrowCongr (cechRingMaximalLocalCohomologyLinearEquiv xs hrad n)
        (LinearEquiv.refl R E))
  have hzero (m : ℕ) : IsZero
      ((((tensorLeft (ModuleCat.of R (R ⧸ maximalIdealSaturatedPower I m))).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology 0) := by
    let M : ModuleCat.{u} R := ModuleCat.of R (R ⧸ maximalIdealSaturatedPower I m)
    let e := cechMaximalLocalCohomologyLinearEquiv xs hrad M 0
    let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R) M 0) :=
      AddCommGrpCat.subsingleton_of_isZero
        (derivedLocalCohomology_maximalIdeal_saturatedPower_quotient_zero I m)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun z w => e.injective (Subsingleton.elim _ _)⟩
  have hΓ : Function.Surjective ((idealPowerTorsionFunctor I).map (D.d 1 0)) :=
    idealPowerTorsion_dual_d_surjective_of_tensor_zero I (maximalIdealSaturatedPower I)
      (exists_maximalIdealSaturatedPower_le_pow I hI hIradical)
      (fun m => ⟨m, pow_le_maximalIdealSaturatedPower I m⟩) E C hzero
  obtain ⟨a, ha, hann⟩ := exists_ne_zero_annihilator_lower_linearMap_localCohomology
    i hi hess (ModuleCat.of R R) (d + 1) hdim.ge
  have hzabove : IsZero (D.X (d + 1 + 1)) := by
    have hC : IsZero (C.X (d + 1 + 1)) :=
      cechLocalizationComplex_isZero_X xs (d + 1 + 1) (by rw [hlen]; exact Nat.lt_succ_self _)
    change IsZero (ModuleCat.of R (C.X (d + 1 + 1) ⟶ E))
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun f g => hC.eq_of_src f g⟩
  let Z : ModuleCat.{u} R := ModuleCat.of R (linearChainCycles D (d + 1))
  let T : ModuleCat.{u} R := ModuleCat.of R
    (derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R R) (d + 1) →ₗ[R] E)
  let eZ : Z ≃ₗ[R] T :=
    (linearChainTopHomologyIso D (d + 1) hzabove).symm.toLinearEquiv.trans (eH (d + 1))
  let : Module.Finite R T :=
    finite_linearMap_localCohomology_maximalIdeal i hi hess (ModuleCat.of R R) (d + 1)
  let : Module.IsTorsionFree R T := isTorsionFree_linearMap_topLocalCohomology E d hdim
  let : Nontrivial T := nontrivial_linearMap_topLocalCohomology i hi (d + 1) hdim
  let : Module.Finite R Z := Module.Finite.equiv eZ.symm
  let : Module.IsTorsionFree R Z :=
    Function.Injective.moduleIsTorsionFree eZ eZ.injective (fun r z => eZ.map_smul r z)
  let : Nontrivial Z := eZ.symm.injective.nontrivial
  let (j : ℕ) : Module.Injective R (D.X j) := by
    let : Module.Flat R (C.X j) := cechLocalizationComplex_flat_X xs j
    exact injective_linearDualComplex_X E C j
  have hZann (z : derivedLocalCohomologyModule I Z (d + 1)) : a ^ d • z = 0 := by
    apply linearChainCycles_localCohomology_pow_smul_eq_zero I D hΓ a d
    intro j hj h
    apply (eH (j + 1)).injective
    rw [map_smul, map_zero]
    exact hann (j + 1) (Nat.add_lt_add_right hj 1) (eH (j + 1) h)
  have hZ : IsZero (derivedLocalCohomology I Z (d + 1)) :=
    derivedLocalCohomology_isZero_of_finite_torsionFree_annihilator
      I Z (d + 1) hdim (a ^ d) (pow_ne_zero d ha) hZann
  exact derivedLocalCohomology_isZero_ring_of_finite_torsionFree I Z (d + 1) hdim hZ

end EtaleFundamentalGroups.Purity

end
