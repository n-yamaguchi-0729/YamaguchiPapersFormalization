/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExactRootFractionDegree
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Nyll.EtaleFundamentalGroups.FiniteEtale.RegularSystem
import Nyll.EtaleFundamentalGroups.Inertia.Galois.RamificationIndexDivisibility
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExactRootRightComparison
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.RegularSystem
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoRegularRing

/-!
# Exact chosen-factor comparison over a complete regular local base

The complete chosen-factor classification is not one-dimensional.  Over a
complete regular local ring `A`, a chosen finite-etale local factor of the
one-root cover is the base change of that cover to the explicit finite-etale
residue lift `C / A`.  A regular system on `A` proves internally that `C` is a
domain and that the image of every parameter is prime.  Consequently the
fraction field of the chosen factor has degree exactly the root exponent over
`Frac(C)`.

This is the two-dimensional form of the degree sandwich used at the
maximal-adic completion.  The base valuation in the final comparison may be
the valuation at the mapped selected height-one parameter; it is deliberately
not required to be the maximal-adic valuation of `A`.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open RingTheory.Sequence
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

/-- The explicit finite residue lift of a complete regular local ring is a
domain.  The regular system, rather than a DVR hypothesis, supplies the
domain structure. -/
theorem finiteEtaleResidueLiftIsDomain_of_regularSystem
    {A l : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = IsLocalRing.maximalIdeal A) :
    IsDomain (FiniteEtaleResidueLift A l) := by
  let C := FiniteEtaleResidueLift A l
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  exact
    (finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := ps) hreg hgen).2.1

/-- Every member of the regular system remains prime in the explicit finite
residue lift. -/
theorem finiteEtaleResidueLift_algebraMap_prime_of_mem_regularSystem
    {A l : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = IsLocalRing.maximalIdeal A)
    (y : A) (hy : y ∈ ps) :
    let C := FiniteEtaleResidueLift A l
    letI : IsDomain C :=
      finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
    Prime (algebraMap A C y) := by
  dsimp only
  let C := FiniteEtaleResidueLift A l
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  have hgeometry :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := ps) hreg hgen
  apply hgeometry.2.2.2.2.2.1 (algebraMap A C y)
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

/-- A root of a member of a regular system over the finite residue lift
again generates a domain. -/
theorem finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
    {A l : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = IsLocalRing.maximalIdeal A)
    {N : ℕ} (hN : 0 < N) (y : A) (hy : y ∈ ps) :
    let C := FiniteEtaleResidueLift A l
    letI : IsDomain C :=
      finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
    IsDomain
      (AdjoinRoot (X ^ N - Polynomial.C (algebraMap A C y))) := by
  dsimp only
  let C := FiniteEtaleResidueLift A l
  let yC := algebraMap A C y
  let psC := ps.map (algebraMap A C)
  let qs := psC.erase yC
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  have hgeometry :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := ps) hreg hgen
  have hyC : yC ∈ psC := List.mem_map.mpr ⟨y, hy, rfl⟩
  have hperm : psC.Perm (yC :: qs) := List.perm_cons_erase hyC
  have hregC : IsRegular C (yC :: qs) :=
    IsLocalRing.isRegular_of_perm hgeometry.2.2.1 hperm
  have hgenC : Ideal.ofList (yC :: qs) = IsLocalRing.maximalIdeal C := by
    rw [← hgeometry.2.2.2.1]
    apply congrArg Ideal.span
    ext z
    exact hperm.mem_iff.symm
  have hymax : yC ∈ IsLocalRing.maximalIdeal C := by
    rw [← hgenC]
    exact Ideal.subset_span List.mem_cons_self
  let : IsLocalRing (AdjoinRoot (X ^ N - Polynomial.C yC)) :=
    isLocalRing_adjoinRoot_X_pow_sub_C hN hymax
  exact (localRootCover_regularSystem_geometry hN hregC hgenC).2.1

/-- The fraction field of a one-root algebra over an arbitrary domain has
degree equal to the exponent when the radicand is prime.

The DVR restriction in the older selected-branch lemma is not used by the
generic-fibre calculation.  Recording the domain-level form is what permits
the same calculation over a two-dimensional finite-etale residue lift. -/
theorem oneRoot_fractionRing_finrank_eq_exponent_of_prime
    {A K F : Type u}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (y : A) (hy : Prime y)
    [Algebra (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [Algebra A F]
    [IsScalarTower A (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsScalarTower A K F] :
    Module.finrank K F = N := by
  have _hy : y ≠ 0 := hy.ne_zero
  let Rn := AdjoinRoot (X ^ N - Polynomial.C y)
  let : IsDomain Rn :=
    (IsFractionRing.injective Rn F).isDomain (algebraMap Rn F)
  let : Module.Free A Rn :=
    (monic_X_pow_sub_C y hN.ne').free_adjoinRoot
  let : Module.Finite A Rn :=
    (monic_X_pow_sub_C y hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[A] Rn) :=
    Module.Finite.base_change A K Rn
  let eFinite : (K ⊗[A] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := A) (C := Rn) (K := K) (E := F)
  calc
    Module.finrank K F = Module.finrank K (K ⊗[A] Rn) :=
      eFinite.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank A Rn := Module.finrank_baseChange
    _ = (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C y hN.ne')).dim := by
      simpa only [Rn] using
        (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C y hN.ne')).finrank
    _ = (X ^ N - Polynomial.C y).natDegree := rfl
    _ = N := Polynomial.natDegree_X_pow_sub_C

/-- Domain-level finite-dimensionality companion to
`oneRoot_fractionRing_finrank_eq_exponent_of_prime`. -/
theorem oneRoot_fractionRing_finiteDimensional_of_prime
    {A K F : Type u}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (y : A) (hy : Prime y)
    [Algebra (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [Algebra A F]
    [IsScalarTower A (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsScalarTower A K F] :
    FiniteDimensional K F := by
  have _hy : y ≠ 0 := hy.ne_zero
  let Rn := AdjoinRoot (X ^ N - Polynomial.C y)
  let : IsDomain Rn :=
    (IsFractionRing.injective Rn F).isDomain (algebraMap Rn F)
  let : Module.Finite A Rn :=
    (monic_X_pow_sub_C y hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[A] Rn) :=
    Module.Finite.base_change A K Rn
  let eFinite : (K ⊗[A] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := A) (C := Rn) (K := K) (E := F)
  exact Module.Finite.equiv eFinite.toLinearEquiv

private theorem finiteDimensional_of_finite_valuationSubrings_regularChosen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, v} K) (target : DVF.{u, w} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional K L := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] L := finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

private theorem compositeAlgebra_toSMul_isScalarTower_regular
    {C K E : Type u}
    [CommRing C] [CommRing K] [CommRing E]
    [Algebra C K] [Algebra K E] :
    @IsScalarTower C K E
      (inferInstance : Algebra C K).toSMul
      (inferInstance : Algebra K E).toSMul
      (((algebraMap K E).comp (algebraMap C K)).toAlgebra).toSMul := by
  refine @IsScalarTower.of_algebraMap_eq C K E
    _ _ _ (inferInstance : Algebra C K)
      (inferInstance : Algebra K E)
      ((algebraMap K E).comp (algebraMap C K)).toAlgebra ?_
  intro x
  rfl

private theorem rootCoordinate_fractionRing_finiteDimensional_finrank
    {C D : Type u} [CommRing C] [IsDomain C]
    [CommRing D] [IsDomain D] [Algebra C D]
    {N : ℕ} (hN : 0 < N) (yC : C)
    [IsDomain (AdjoinRoot (X ^ N - Polynomial.C yC))]
    [Module.Free C (AdjoinRoot (X ^ N - Polynomial.C yC))]
    [FaithfulSMul C (AdjoinRoot (X ^ N - Polynomial.C yC))]
    (eRoot : AdjoinRoot (X ^ N - Polynomial.C yC) ≃ₐ[C] D) :
    letI : Algebra C (FractionRing D) :=
      fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
    letI : Algebra (FractionRing C) (FractionRing D) :=
      fractionRingAlgebraOfAlgEquiv eRoot
    FiniteDimensional (FractionRing C) (FractionRing D) ∧
      Module.finrank (FractionRing C) (FractionRing D) = N := by
  let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
  let : Module.Finite C Rn :=
    (monic_X_pow_sub_C yC hN.ne').finite_adjoinRoot
  let : Module.Free C D := Module.Free.of_equiv eRoot.toLinearEquiv
  let : Module.Finite C D := Module.Finite.equiv eRoot.toLinearEquiv
  let KC := FractionRing C
  let P := FractionRing D
  let : Algebra C P := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C P
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
  let : @IsScalarTower C KC P
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Module.Finite KC (KC ⊗[C] D) := Module.Finite.base_change C KC D
  let eGeneric : (KC ⊗[C] D) ≃ₐ[KC] P :=
    finiteGenericFiberAlgEquiv (R := C) (C := D) (K := KC) (E := P)
  refine ⟨Module.Finite.equiv eGeneric.toLinearEquiv, ?_⟩
  calc
    Module.finrank KC P = Module.finrank KC (KC ⊗[C] D) :=
      eGeneric.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank C D := Module.finrank_baseChange
    _ = Module.finrank C Rn := eRoot.toLinearEquiv.finrank_eq.symm
    _ = (AdjoinRoot.powerBasis' (monic_X_pow_sub_C yC hN.ne')).dim := by
      exact (AdjoinRoot.powerBasis' (monic_X_pow_sub_C yC hN.ne')).finrank
    _ = (X ^ N - Polynomial.C yC).natDegree := rfl
    _ = N := Polynomial.natDegree_X_pow_sub_C

/-- A chosen finite-etale local factor of a one-root cover over a complete
regular local ring has exact fraction degree after the explicit finite
residue lift.

The tensor coordinate, the domain structure on the lift, and primality of the
mapped selected parameter are all source-produced. -/
theorem
    exists_completeRegularLocalChosenFactor_oneRoot_fractionRing_finrank_eq_exponent
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N) (y : A) (hy : y ∈ ps) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span hy
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            letI : IsDomain Rn :=
              finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
                hreg hgen hN y hy
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            letI : Algebra C (FractionRing D) :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : Algebra (FractionRing C) (FractionRing D) :=
              fractionRingAlgebraOfAlgEquiv eRoot
            Module.finrank (FractionRing C) (FractionRing D) = N := by
  intro n a B hymax D _ _ _ _ _ _ q _ _ hunique k kB l eResidue C
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) (fun _ ↦ hymax)
  let : Module.Finite A B := finite_iteratedRadical n a (fun _ ↦ hN)
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  let : IsLocalRing D := isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB := AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  obtain ⟨eTensor, _⟩ :=
    exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      n a (fun _ ↦ hN) (fun _ ↦ hymax) (D := D) q hunique
  refine ⟨eTensor, ?_⟩
  let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  intro yC Rn eRoot
  let : IsDomain Rn :=
    finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
      hreg hgen hN y hy
  let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C Rn :=
    (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
  let : FaithfulSMul C Rn := inferInstance
  exact (rootCoordinate_fractionRing_finiteDimensional_finrank hN yC eRoot).2

/-- Two-dimensional complete-local exact-degree sandwich.

After producing the finite residue lift and its chosen-factor coordinate, any
compatible intermediate field whose selected height-one ramification index is
the root exponent is already the whole chosen-factor fraction field.  No
fraction-degree equality or right-map bijectivity is a public input. -/
theorem
    exists_completeRegularLocalChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactRamification
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {ps : List A}
    (hreg : IsRegular A ps)
    (hgen : Ideal.ofList ps = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N) (y : A) (hy : y ∈ ps) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span hy
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            letI : IsDomain Rn :=
              finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
                hreg hgen hN y hy
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            letI : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
            letI : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
            letI : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            letI : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
            ∀ {Omega : Type u} [Field Omega]
              [Algebra KC Omega] [Algebra Omega P]
              [IsScalarTower KC Omega P],
              ∀ (base : DVF.{u, v} KC) (target : DVF.{u, w} Omega)
                [base.valuation.HasExtension target.valuation]
                [Module.Finite base.valuationSubring
                  target.valuationSubring],
                ramificationIndex base target = N →
                  Function.Bijective (algebraMap Omega P) := by
  intro n a B hymax D _ _ _ _ _ _ q _ _ hunique k kB l eResidue C
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) (fun _ ↦ hymax)
  let : Module.Finite A B := finite_iteratedRadical n a (fun _ ↦ hN)
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  let : IsLocalRing D := isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB := AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  obtain ⟨eTensor, hDegree⟩ :=
    exists_completeRegularLocalChosenFactor_oneRoot_fractionRing_finrank_eq_exponent
      hreg hgen N hN y hy (D := D) q hunique
  refine ⟨eTensor, ?_⟩
  let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  intro yC Rn eRoot P KC
  let : IsDomain Rn :=
    finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
      hreg hgen hN y hy
  let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C Rn :=
    (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
  let : FaithfulSMul C Rn := inferInstance
  let : Algebra C P := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C P
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
  let : @IsScalarTower C KC P
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
  let : FiniteDimensional KC P :=
    (rootCoordinate_fractionRing_finiteDimensional_finrank hN yC eRoot).1
  intro Omega _ _ _ _ base target _ _ hExact
  let : FiniteDimensional KC Omega :=
    finiteDimensional_of_finite_valuationSubrings_regularChosen base target
  let i : Omega →ₗ[KC] P :=
    (Algebra.linearMap Omega P).restrictScalars KC
  have hi : Function.Injective i := (algebraMap Omega P).injective
  have hOmegaLeP : Module.finrank KC Omega ≤ Module.finrank KC P :=
    i.finrank_le_finrank_of_injective hi
  have hRamLeOmega : N ≤ Module.finrank KC Omega := by
    rw [← hExact]
    exact ramificationIndex_le_finrank_of_moduleFinite base target
  have hFinrankEq : Module.finrank KC Omega = Module.finrank KC P := by
    have hP : Module.finrank KC P = N := by
      simpa only [P, KC] using hDegree
    omega
  have hiSurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hFinrankEq).mp hi
  refine ⟨(algebraMap Omega P).injective, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := hiSurjective z
  exact ⟨x, hx⟩

/-- Two-dimensional complete-local degree sandwich with an integral
normalization prime as its exact-ramification input.

Here the intermediate field is not arbitrary: it is the literal component
of a base change of a finite Galois extension.  Hence its Galois and finite
dimensional structures over `Frac(C)` are produced by
`genericTensorFieldComponentIsGalois`.  Divisibility of the exact
normalization ramification index by the field degree replaces all valued
field and finite-valuation-subring inputs of the older comparison theorem. -/
theorem
exists_completeRegularLocalChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactNormalizationPrime
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A))) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span List.mem_cons_self
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            letI : IsDomain Rn :=
              finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
                hreg hgen hN y List.mem_cons_self
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            letI : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
            letI : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
            letI : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            letI : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
            ∀ {K₀ L₀ : Type u} [Field K₀] [Field L₀]
              [Algebra K₀ KC] [Algebra K₀ L₀]
              [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀],
              ∀ (m : Ideal (KC ⊗[K₀] L₀)) (hm : m.IsMaximal),
                letI : m.IsMaximal := hm
                let Omega := GenericTensorFieldComponent m
                let cOmegaAlgebra : Algebra C Omega :=
                  ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
                let : @IsScalarTower C KC Omega
                    (inferInstance : Algebra C KC).toSMul
                    (inferInstance : Algebra KC Omega).toSMul
                    cOmegaAlgebra.toSMul :=
                  compositeAlgebra_toSMul_isScalarTower_regular
                ∀ [Algebra Omega P] [IsScalarTower KC Omega P],
                  let pC := Ideal.span ({yC} : Set C)
                  ∀ (Q : Ideal (integralClosure C Omega)) [Q.IsPrime]
                    [Q.LiesOver pC],
                    Q.ramificationIdx C = N →
                      Function.Bijective (algebraMap Omega P) := by
  intro n a B hymax D _ _ _ _ _ _ q _ _ hunique k kB l eResidue C
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) (fun _ ↦ hymax)
  let : Module.Finite A B := finite_iteratedRadical n a (fun _ ↦ hN)
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  let : IsLocalRing D := isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB := AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  obtain ⟨eTensor, hDegree⟩ :=
    exists_completeRegularLocalChosenFactor_oneRoot_fractionRing_finrank_eq_exponent
      hreg hgen N hN y (by exact List.mem_cons_self) (D := D) q hunique
  refine ⟨eTensor, ?_⟩
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  intro yC Rn eRoot P KC
  let : IsDomain Rn :=
    finiteEtaleResidueLift_adjoinRoot_isDomain_of_mem_regularSystem
      hreg hgen hN y (by exact List.mem_cons_self)
  let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C Rn :=
    (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
  let : FaithfulSMul C Rn := inferInstance
  let : Algebra C P := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C P
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
  let : @IsScalarTower C KC P
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
  have hyC : Prime yC :=
    finiteEtaleResidueLift_algebraMap_prime_of_mem_regularSystem
      hreg hgen y (by exact List.mem_cons_self)
  let : FiniteDimensional KC P :=
    (rootCoordinate_fractionRing_finiteDimensional_finrank hN yC eRoot).1
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsNoetherianRing C := hgeometryC.1
  let : IsRegularLocalRing C := hgeometryC.2.2.2.2.1
  have hdimAux :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
      ([y, z].map (algebraMap A C)) hgeometryC.2.2.1
  rw [hgeometryC.2.2.2.1] at hdimAux
  let : Field (C ⧸ IsLocalRing.maximalIdeal C) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal C)
  have hfieldDim :
      ringKrullDim (C ⧸ IsLocalRing.maximalIdeal C) = 0 :=
    ringKrullDim_eq_zero_of_field _
  rw [hfieldDim, zero_add] at hdimAux
  have hdimC :
      ringKrullDim C = ((2 : ℕ∞) : WithBot ℕ∞) := by
    norm_num [List.length_cons, List.length_nil] at hdimAux
    exact hdimAux.symm
  intro K₀ L₀ _ _ _ _ _ _ m hm
  let : m.IsMaximal := hm
  intro Omega cOmegaAlgebra hCOmegaTower _ _ pC
  let : pC.IsPrime := Ideal.isPrime_span_singleton_of_prime hyC
  intro Q _ _ hExact
  have hpCHeight : pC.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hyC.ne_zero) hyC.not_isUnit
  let : IsRegularRing C :=
    EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_two hdimC
  let pA := Ideal.span ({y} : Set A)
  have hpMap : pA.map (algebraMap A C) = pC := by
    simp only [pA, pC, yC, Ideal.map_span, Set.image_singleton]
  have hCharCMap :
      CharZero (C ⧸ pA.map (algebraMap A C)) := by
    let J := pA.map (algebraMap A C)
    have hUnder : J.under A = pA :=
      Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) pA
    let : CharZero (A ⧸ J.under A) := by
      rw [hUnder]
      exact hCharZero
    exact charZero_of_injective_algebraMap
      (Ideal.algebraMap_quotient_injective (R := A) (A := C) (I := J))
  let : CharZero (C ⧸ pC) :=
    (congrArg (fun J : Ideal C => CharZero (C ⧸ J)) hpMap).mp hCharCMap
  let : FiniteDimensional KC Omega :=
    genericTensorFieldComponentFiniteDimensional (K := K₀) (K' := KC) (L := L₀) m
  let : IsGalois KC Omega :=
    genericTensorFieldComponentIsGalois (K := K₀) (K' := KC) (L := L₀) m
  have hRamDiv : N ∣ Module.finrank KC Omega := by
    have hRam : Q.ramificationIdx C ∣ Module.finrank KC Omega :=
      normalization_ramificationIdx_dvd_finrank_of_charZero
        (A := C) (K := KC) (L := Omega) pC hpCHeight Q
    exact
      (congrArg (fun e => e ∣ Module.finrank KC Omega) hExact).mp hRam
  let i : Omega →ₗ[KC] P :=
    (Algebra.linearMap Omega P).restrictScalars KC
  have hi : Function.Injective i := (algebraMap Omega P).injective
  have hOmegaLeP : Module.finrank KC Omega ≤ Module.finrank KC P :=
    i.finrank_le_finrank_of_injective hi
  have hRamLeOmega : N ≤ Module.finrank KC Omega :=
    Nat.le_of_dvd Module.finrank_pos hRamDiv
  have hFinrankEq : Module.finrank KC Omega = Module.finrank KC P := by
    have hP : Module.finrank KC P = N := by
      simpa only [P, KC] using hDegree
    omega
  have hiSurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hFinrankEq).mp hi
  refine ⟨(algebraMap Omega P).injective, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := hiSurjective z
  exact ⟨x, hx⟩

end EtaleFundamentalGroups.Kummer

end
