/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Degree-zero nonvanishing for derived local cohomology

The degree-zero base case of Grothendieck nonvanishing is already visible in
the ideal-powers Ext diagram.  For the zero ideal, every positive power is
again zero, and the identity class of `R ⧸ (0)` survives every later
transition.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

/-- The quotient map between two positive powers of the zero ideal is the
canonical isomorphism induced by equality of those powers. -/
private theorem ringModIdeals_bot_transition_eq_quotEquiv
    {R : Type u} [CommRing R]
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≤ m) :
    (localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram (⊥ : Ideal R))).map
        (homOfLE hnm).op =
      (Submodule.quotEquivOfEq
        ((⊥ : Ideal R) ^ m) ((⊥ : Ideal R) ^ n)
        (by simp [Ideal.bot_pow (Nat.ne_of_gt hn),
          Ideal.bot_pow (Nat.ne_of_gt hm)])).toModuleIso.hom := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [localCohomology.ringModIdeals,
        localCohomology.idealPowersDiagram]
      rfl

/-- Derived local cohomology supported at the zero ideal is nonzero in
degree zero over every nontrivial commutative ring. -/
theorem derivedLocalCohomology_bot_not_isZero_zero
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ IsZero
      (derivedLocalCohomology (⊥ : Ideal R) (ModuleCat.of R R) 0) := by
  rw [derivedLocalCohomology_not_isZero_iff_exists_persistent_transition]
  let eIso : ModuleCat.of R (R ⧸ (⊥ : Ideal R) ^ 1) ≅ ModuleCat.of R R :=
    (Submodule.quotEquivOfEqBot
      ((⊥ : Ideal R) ^ 1) (by simp)).toModuleIso
  let e : ModuleCat.of R (R ⧸ (⊥ : Ideal R) ^ 1) ⟶ ModuleCat.of R R :=
    eIso.hom
  have he : e ≠ 0 := by
    intro hzero
    have hid : 𝟙 (ModuleCat.of R R) = 0 := by
      calc
        𝟙 (ModuleCat.of R R) = eIso.inv ≫ eIso.hom :=
          eIso.inv_hom_id.symm
        _ = 0 := by
          change eIso.inv ≫ e = 0
          rw [hzero, comp_zero]
    have hone := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hid) (1 : R)
    change (1 : R) = 0 at hone
    exact (one_ne_zero : (1 : R) ≠ 0) hone
  refine ⟨1,
    CategoryTheory.Abelian.Ext.mk₀ e, ?_⟩
  intro m hnm
  have hm : 1 ≤ m := hnm
  have : IsIso
      ((localCohomology.ringModIdeals
        (localCohomology.idealPowersDiagram (⊥ : Ideal R))).map
          (homOfLE hnm).op) := by
    rw [ringModIdeals_bot_transition_eq_quotEquiv
      (R := R) (n := 1) (m := m) (by omega) hm hnm]
    exact Iso.isIso_hom _
  have : IsIso
      ((derivedLocalCohomologyPowersDiagram
        (⊥ : Ideal R) (ModuleCat.of R R) 0).map
          (homOfLE hnm).op.op) := by
    change IsIso
      ((derivedExtContravariantFunctor (ModuleCat.of R R) 0).map
        (((localCohomology.ringModIdeals
          (localCohomology.idealPowersDiagram (⊥ : Ideal R))).map
            (homOfLE hnm).op).op))
    exact
      (derivedExtContravariantFunctor (ModuleCat.of R R) 0).map_isIso _
  intro hzero
  apply (CategoryTheory.Abelian.Ext.mk₀_eq_zero_iff e).not.mpr he
  apply
    (ConcreteCategory.bijective_of_isIso
      ((derivedLocalCohomologyPowersDiagram
        (⊥ : Ideal R) (ModuleCat.of R R) 0).map
          (homOfLE hnm).op.op)).1
  exact hzero.trans (map_zero _).symm

/-- Grothendieck nonvanishing in dimension zero: a zero-dimensional local
domain is a field, so its maximal ideal is zero and the preceding persistent
degree-zero class applies. -/
theorem derivedLocalCohomology_maximalIdeal_not_isZero_zero_of_ringKrullDim_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0) :
    ¬ IsZero
      (derivedLocalCohomology (IsLocalRing.maximalIdeal R)
        (ModuleCat.of R R) 0) := by
  let : Ring.KrullDimLE 0 R :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  have hmax : IsLocalRing.maximalIdeal R = ⊥ := by
    exact
      (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime
        (⊥ : Ideal R)).symm
  rw [hmax]
  exact derivedLocalCohomology_bot_not_isZero_zero

/-- Hartshorne--Lichtenbaum vanishing is vacuous in dimension zero: a
radical ideal distinct from the unique maximal ideal must be the unit ideal. -/
theorem derivedLocalCohomology_isZero_of_isRadical_ne_maximalIdeal_of_ringKrullDim_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0)
    (J : Ideal R) (hJradical : J.IsRadical)
    (hJnonmax : J ≠ IsLocalRing.maximalIdeal R) (i : ℕ) :
    IsZero (derivedLocalCohomology J (ModuleCat.of R R) i) := by
  let : Ring.KrullDimLE 0 R :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  have hJtop : J = ⊤ := by
    by_contra hJproper
    apply hJnonmax
    rw [← hJradical.radical]
    exact Ring.KrullDimLE.radical_eq_maximalIdeal J hJproper
  rw [hJtop]
  exact derivedLocalCohomology_top_isZero (ModuleCat.of R R) i

end EtaleFundamentalGroups

end
