/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import EtaleFundamentalGroups.Completions.Chosen.DVRProductCoordinate
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import SchemeTheory.Normalization.Products.LocalRingFactor

/-!
# Exhaustion of completed generic tensor components

For a finite Dedekind extension of a DVR, every maximal component of the
completed generic tensor product is the component canonically selected by a
unique completed local coordinate (existence is all that is needed here).

The proof works on the finite completed model.  It closes the contracted
generic prime over the completed base DVR, uses the product decomposition to
identify its coordinate, and then uses uniqueness of the generic prime below
that coordinate maximal ideal.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uV uC uK uL

/-- Contracting a proper ideal of the localization by the nonzero base
scalars gives the zero ideal in the base domain. -/
private theorem under_eq_bot_of_localized_nonZeroDivisors
    (R : Type*) (B : Type*) (S : Type*)
    [CommSemiring R] [IsDomain R]
    [instB : CommSemiring B] [instS : CommSemiring S]
    [Algebra R B] [Algebra B S]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) S]
    (J : Ideal S) (hJ : J ≠ ⊤) : (J.under B).under R = ⊥ := by
  apply le_antisymm
  · intro z hz
    by_contra hz0
    have hzM : algebraMap R B z ∈
        Algebra.algebraMapSubmonoid B (nonZeroDivisors R) :=
      ⟨z, mem_nonZeroDivisors_iff_ne_zero.mpr hz0, rfl⟩
    have hzJ : algebraMap B S (algebraMap R B z) ∈ J := hz
    have hu : IsUnit (algebraMap B S (algebraMap R B z)) :=
      IsLocalization.map_units
        (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) S
        ⟨algebraMap R B z, hzM⟩
    exact hJ (J.eq_top_of_isUnit_mem hzJ hu)
  · exact bot_le

/-- A maximal ideal of a product is the coordinate maximal ideal when its
    given coordinate prime contracts to that product ideal. -/
private theorem coordinate_prime_eq_of_maximal_comap
    {ι : Type*} (A : ι → Type*)
    [∀ j, CommRing (A j)] [∀ j, IsLocalRing (A j)]
    (P : Ideal (∀ j, A j)) (hP : P.IsMaximal)
    (i : ι) (q : PrimeSpectrum (A i))
    (hq : q.asIdeal.comap (Pi.evalRingHom A i) = P) :
    P = productCoordinatePrime A i := by
  have hMapped :
      (q.asIdeal.comap (Pi.evalRingHom A i)).map (Pi.evalRingHom A i) =
        q.asIdeal :=
    Ideal.map_comap_of_surjective (Pi.evalRingHom A i)
      (Pi.evalRingHom A i).surjective q.asIdeal
  have hComapMax : (q.asIdeal.comap (Pi.evalRingHom A i)).IsMaximal :=
    hq.symm ▸ hP
  have hOr := Ideal.map_eq_top_or_isMaximal_of_surjective
    (Pi.evalRingHom A i) (Pi.evalRingHom A i).surjective hComapMax
  have hMappedMax :=
    hOr.resolve_left (fun h => q.isPrime.ne_top (hMapped.symm.trans h))
  have hqmax : q.asIdeal.IsMaximal := hMapped ▸ hMappedMax
  have hqeq : q.asIdeal = IsLocalRing.maximalIdeal (A i) :=
    (IsLocalRing.isMaximal_iff (R := A i)).mp hqmax
  exact hq.symm.trans
    (congrArg (fun I : Ideal (A i) => I.comap (Pi.evalRingHom A i)) hqeq)

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- Every maximal ideal of the completed generic tensor product is the
canonical ideal selected by some prime of `C` above the closed point of
`V`. -/
theorem exists_completedGenericTensorChosenIdeal_eq
    :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : IsLocalHom (algebraMap V Vhat) :=
      standardDVRToCompletion_isLocalHom V K
    letI : Module.FaithfullyFlat V Vhat :=
      standardDVRCompletionValuationSubring_faithfullyFlat
        (V := V) (K := K)
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
    letI : Algebra V Khat :=
      standardDVFCompletionBaseAlgebra (V := V) (K := K)
    letI : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
    letI : Module K Khat :=
      (standardDVFCompletionAlgebra V K).toModule
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    letI : Module V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toModule
    letI : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    letI : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    let G := Khat ⊗[K] L
    ∀ m : Ideal G, m.IsMaximal →
      ∃ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
      let hres := standardDVRToCompletion_residueFieldMap_bijective V K
      completedGenericTensorChosenIdeal
        (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
        hmax hres Q.1 = m := by
  classical
  intro H Vhat Khat
  let p := IsLocalRing.maximalIdeal V
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V Vhat) :=
    standardDVRToCompletion_isLocalHom V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
  let : Module K Khat :=
    (standardDVFCompletionAlgebra V K).toModule
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : Module V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toModule
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  intro G m hm
  let : m.IsMaximal := hm
  let U := Vhat ⊗[V] C
  let G₀ := Khat ⊗[Vhat] U
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : Algebra U G₀ := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower Vhat U G₀ :=
    Algebra.TensorProduct.right_isScalarTower
  let M : Submonoid U :=
    Algebra.algebraMapSubmonoid U (nonZeroDivisors Vhat)
  let : IsLocalization M G₀ :=
    IsLocalization.tensorRight (R := Vhat) (S := U) (A := Khat)
      (nonZeroDivisors Vhat)
  let eOriginal : G₀ ≃ₐ[Khat] G := completedGenericFiberEquiv
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
  let m₀ : Ideal G₀ := m.comap eOriginal.toRingEquiv.toRingHom
  let : m₀.IsMaximal :=
    (inferInstance : m.IsMaximal).comap_bijective
      eOriginal.toRingEquiv.toRingHom eOriginal.bijective
  let : m₀.IsPrime := by
    change (m.comap eOriginal.toRingEquiv.toRingHom).IsPrime
    exact (inferInstance : m.IsMaximal).isPrime.comap eOriginal.toRingEquiv.toRingHom
  let N : Ideal U := genericFiberComponentBaseIdeal m₀
  let : N.IsPrime := (inferInstance : m₀.IsPrime).comap
    (Algebra.TensorProduct.includeRight : U →ₐ[Vhat] G₀).toRingHom
  have hNunder : N.under Vhat = ⊥ := by
    have hN_eq_under : N = m₀.under U := rfl
    exact (congrArg (fun I : Ideal U => I.under Vhat) hN_eq_under).trans
      (under_eq_bot_of_localized_nonZeroDivisors Vhat U G₀
        (instB := Algebra.TensorProduct.instCommSemiring (R := V) (A := Vhat) (B := C))
        (instS := Algebra.TensorProduct.instCommSemiring (R := Vhat) (A := Khat) (B := U))
        m₀ (inferInstance : m₀.IsPrime).ne_top)
  let : N.LiesOver (⊥ : Ideal Vhat) := ⟨hNunder.symm⟩
  let : Module.Finite Vhat U := Module.Finite.base_change V Vhat C
  let : Algebra.IsIntegral Vhat U := Algebra.IsIntegral.of_finite Vhat U
  have hNmax : N.under Vhat ≤ IsLocalRing.maximalIdeal Vhat := by
    rw [hNunder]
    exact bot_le
  obtain ⟨P, hNP, hPPrime, hPcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (IsLocalRing.maximalIdeal Vhat) N hNmax
  let : P.IsPrime := hPPrime
  let : P.LiesOver (IsLocalRing.maximalIdeal Vhat) :=
    (Ideal.liesOver_iff P (IsLocalRing.maximalIdeal Vhat)).mpr hPcomap.symm
  let : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P
    (IsLocalRing.maximalIdeal Vhat)
  let A := fun Q : p.primesOver C ↦
    completedPrimeValuationSubring (L := L) Q
  let : ∀ Q, Algebra Vhat (A Q) := fun Q ↦
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q
  let E := completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
    (V := V) (C := C) (K := K) (L := L)
  let Pprod := P.map E.toRingEquiv.toRingHom
  let : Pprod.IsMaximal :=
    (inferInstance : P.IsMaximal).map_bijective
      E.toRingEquiv.toRingHom E.bijective
  let pSpec : PrimeSpectrum (∀ Q : p.primesOver C, A Q) :=
    ⟨Pprod, (inferInstance : Pprod.IsMaximal).isPrime⟩
  obtain ⟨Q, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq pSpec
  have hqcomap : q.asIdeal.comap (Pi.evalRingHom A Q) = Pprod :=
    congrArg PrimeSpectrum.asIdeal hq
  have hPprod : Pprod = productCoordinatePrime A Q :=
    coordinate_prime_eq_of_maximal_comap A Pprod
      (inferInstance : Pprod.IsMaximal) Q q hqcomap
  let Nprod := N.map E.toRingEquiv.toRingHom
  let : Nprod.IsPrime := by
    apply Ideal.map_isPrime_of_surjective E.surjective
    intro x hx
    have hx0 : x = 0 := E.injective (hx.trans E.map_zero.symm)
    simp only [hx0, Ideal.zero_mem]
  have hNprodP : Nprod ≤ productCoordinatePrime A Q := by
    rw [← hPprod]
    exact Ideal.map_mono hNP
  have hNneP : N ≠ P := by
    intro hEq
    have : (⊥ : Ideal Vhat) = IsLocalRing.maximalIdeal Vhat := by
      calc
        (⊥ : Ideal Vhat) = N.under Vhat := hNunder.symm
        _ = P.under Vhat := by rw [hEq]
        _ = IsLocalRing.maximalIdeal Vhat :=
          (P.over_def (IsLocalRing.maximalIdeal Vhat)).symm
    exact IsDiscreteValuationRing.not_a_field Vhat this.symm
  have hNprodNe : Nprod ≠ productCoordinatePrime A Q := by
    intro hEq
    exact hNneP (E.toRingEquiv.idealComapOrderIso.symm.injective
      (hEq.trans hPprod.symm))
  have hNprod : Nprod = RingHom.ker (Pi.evalRingHom A Q) :=
    prime_eq_ker_coordinateEval_of_le_of_ne A Q Nprod hNprodP hNprodNe
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let NQ := completedBaseChangeChosenGenericPrime
    (R := V) (R' := Vhat) hmax hres Q.1
  have hNQprod : NQ.map E.toRingEquiv.toRingHom =
      RingHom.ker (Pi.evalRingHom A Q) :=
    (completedBaseChangeChosenPrimes_map_localFactors
      (V := V) (C := C) (K := K) (L := L) Q).2
  have hNNQ : N = NQ := by
    calc
      N = (N.map E.toRingEquiv.toRingHom).comap
          E.toRingEquiv.toRingHom :=
        (Ideal.comap_map_of_bijective
          E.toRingEquiv.toRingHom E.bijective).symm
      _ = (NQ.map E.toRingEquiv.toRingHom).comap
          E.toRingEquiv.toRingHom :=
        congrArg (fun I ↦ I.comap E.toRingEquiv.toRingHom)
          (hNprod.trans hNQprod.symm)
      _ = NQ := Ideal.comap_map_of_bijective
        E.toRingEquiv.toRingHom E.bijective
  let mQ₀ : Ideal G₀ := completedBaseChangeChosenGenericIdeal
    (R := V) (R' := Vhat) (K' := Khat) hmax hres Q.1
  have hm₀under : m₀.under U = N := rfl
  have hmQ₀under : mQ₀.under U = NQ :=
    completedBaseChangeChosenGenericIdeal_comap
      (R := V) (R' := Vhat) (K' := Khat) hmax hres Q.1
  have hm₀mQ₀ : m₀ = mQ₀ := by
    apply (IsLocalization.orderEmbedding M G₀).injective
    change m₀.under U = mQ₀.under U
    exact hm₀under.trans (hNNQ.trans hmQ₀under.symm)
  refine ⟨Q, ?_⟩
  change mQ₀.map eOriginal.toRingEquiv.toRingHom = m
  calc
    mQ₀.map eOriginal.toRingEquiv.toRingHom =
        m₀.map eOriginal.toRingEquiv.toRingHom := by rw [hm₀mQ₀]
    _ = m := Ideal.map_comap_of_surjective
      eOriginal.toRingEquiv.toRingHom eOriginal.surjective m

end EtaleFundamentalGroups
