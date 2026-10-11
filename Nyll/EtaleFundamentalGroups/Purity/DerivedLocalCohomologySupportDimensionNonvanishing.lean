/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyArtinian
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalarQuotient
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionZero
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopFinite
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionFreeQuotient
import Nyll.EtaleFundamentalGroups.Purity.MaximalIdealTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.RegularArtinianParameterChoice
import Nyll.EtaleFundamentalGroups.Purity.TorsionQuotientSupportDimension
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Monoid
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.Category

/-!
# Top local-cohomology nonvanishing for finite coefficients

Over a complete Noetherian local ring, a finite module of finite support
dimension has nonzero local cohomology in that dimension.  In positive
dimension the top local-cohomology module is not finitely generated.

The two conclusions are proved together by induction on dimension.
Removing the maximal-ideal-primary component preserves positive support
dimension and positive local cohomology.  A regular scalar can then be
chosen whose quotient on the preceding Artinian cohomology has finite
length.  Vanishing in the top degree would contradict the induction
hypothesis on the coefficient scalar quotient.  Finite generation in
the top degree would force that vanishing by Nakayama's lemma.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [IsAdicComplete (maximalIdeal R) R]

private theorem topLocalCohomology_nonzero_and_notFinite
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (hdim : Module.supportDim R M = (d : WithBot ℕ∞)) :
    (¬ IsZero (derivedLocalCohomology (maximalIdeal R) M d)) ∧
      (d ≠ 0 → ¬ Module.Finite R
        (derivedLocalCohomologyModule (maximalIdeal R) M d)) := by
  induction d generalizing M with
  | zero =>
      refine ⟨derivedLocalCohomology_maximalIdeal_not_isZero_of_supportDim_eq_zero M hdim, ?_⟩
      intro hne
      exact False.elim (hne rfl)
  | succ d ih =>
      let T : Submodule R M := Ideal.primaryComponent M (maximalIdeal R)
      let Q : ModuleCat.{u} R := ModuleCat.of R (M ⧸ T)
      let : Module.Finite R Q := by
        change Module.Finite R (M ⧸ T)
        infer_instance
      have hpos : 0 < Module.supportDim R M := by
        rw [hdim]
        exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.zero_lt_succ d))
      have hdimQ : Module.supportDim R Q = ((d + 1 : ℕ) : WithBot ℕ∞) :=
        (Purity.supportDim_quotient_primaryComponent_maximalIdeal_eq_of_pos hpos).trans hdim
      let eT : derivedLocalCohomologyModule (maximalIdeal R) M (d + 1) ≃ₗ[R]
          derivedLocalCohomologyModule (maximalIdeal R) Q (d + 1) :=
        derivedLocalCohomologyModuleEquiv_succ_quotient_primaryComponent
          (maximalIdeal R) M d
      let : IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R) Q d) :=
        isArtinian_derivedLocalCohomologyModule_maximalIdeal Q d
      obtain ⟨x, hx, hreg, hlength⟩ :=
        Purity.exists_regular_mem_maximalIdeal_finiteLength_quotient Q
          (derivedLocalCohomologyModule (maximalIdeal R) Q d)
          (Purity.maximalIdeal_not_mem_associatedPrimes_quotient_primaryComponent
            (R := R) (M := M))
      let W : ModuleCat.{u} R := (Q.smulShortComplex x).X₃
      let : Module.Finite R W := by
        change Module.Finite R (Q ⧸ x • (⊤ : Submodule R Q))
        infer_instance
      have hdimW : Module.supportDim R W = (d : WithBot ℕ∞) := by
        apply ENat.WithBot.add_one_cancel.mp
        calc
          Module.supportDim R W + 1 = Module.supportDim R Q :=
            Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx
          _ = ((d + 1 : ℕ) : WithBot ℕ∞) := hdimQ
          _ = (d : WithBot ℕ∞) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      have hW := ih W hdimW
      have hQnonzero : ¬ IsZero (derivedLocalCohomology (maximalIdeal R) Q (d + 1)) := by
        intro hzero
        let e : (derivedLocalCohomologyModule (maximalIdeal R) Q d ⧸
            x • (⊤ : Submodule R (derivedLocalCohomologyModule (maximalIdeal R) Q d))) ≃ₗ[R]
              derivedLocalCohomologyModule (maximalIdeal R) W d :=
          derivedLocalCohomologyModuleScalarQuotientEquiv (maximalIdeal R) Q d x hreg hzero
        by_cases hd : d = 0
        · subst d
          let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R) Q 0) :=
            AddCommGrpCat.subsingleton_of_isZero
              (derivedLocalCohomology_maximalIdeal_isZero_zero_quotient_primaryComponent M)
          apply hW.1
          apply AddCommGrpCat.isZero_iff_subsingleton.mpr
          exact ⟨fun z w => e.symm.injective (Subsingleton.elim _ _)⟩
        · have hWlength : IsFiniteLength R
              (derivedLocalCohomologyModule (maximalIdeal R) W d) :=
            hlength.of_surjective (f := e.toLinearMap) e.surjective
          let : IsNoetherian R
              (derivedLocalCohomologyModule (maximalIdeal R) W d) :=
            (isFiniteLength_iff_isNoetherian_isArtinian.mp hWlength).1
          exact hW.2 hd inferInstance
      refine ⟨?_, ?_⟩
      · intro hzero
        let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R) M (d + 1)) :=
          AddCommGrpCat.subsingleton_of_isZero hzero
        apply hQnonzero
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        exact ⟨fun z w => eT.symm.injective (Subsingleton.elim _ _)⟩
      · intro _hd hfinite
        let : Module.Finite R
            (derivedLocalCohomologyModule (maximalIdeal R) M (d + 1)) := hfinite
        let : Module.Finite R
            (derivedLocalCohomologyModule (maximalIdeal R) Q (d + 1)) :=
          Module.Finite.of_surjective eT.toLinearMap eT.surjective
        exact hQnonzero
          (derivedLocalCohomology_maximalIdeal_isZero_succ_of_finite_of_regular
            Q d hdimQ x hx hreg)

/-- A finite module of finite support dimension has nonzero local
cohomology in that degree over a complete Noetherian local ring. -/
theorem derivedLocalCohomology_maximalIdeal_not_isZero_of_supportDim_eq
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (hdim : Module.supportDim R M = (d : WithBot ℕ∞)) :
    ¬ IsZero (derivedLocalCohomology (maximalIdeal R) M d) :=
  (topLocalCohomology_nonzero_and_notFinite M d hdim).1

/-- Top local cohomology in positive finite support dimension is not a
finite module over a complete Noetherian local ring. -/
theorem not_moduleFinite_derivedLocalCohomologyModule_maximalIdeal_of_supportDim_eq
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ) (hd : 0 < d)
    (hdim : Module.supportDim R M = (d : WithBot ℕ∞)) :
    ¬ Module.Finite R (derivedLocalCohomologyModule (maximalIdeal R) M d) :=
  (topLocalCohomology_nonzero_and_notFinite M d hdim).2 (ne_of_gt hd)

end EtaleFundamentalGroups
