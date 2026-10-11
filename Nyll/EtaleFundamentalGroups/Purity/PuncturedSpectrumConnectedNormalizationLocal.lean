/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumHypersurfaceAmbientIdeals
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite

/-!
# Locality of connected finite normalizations over complete local rings

A finite domain algebra over a complete Noetherian local ring is local.  The
proof passes to the closed fibre: completeness lifts idempotents, so the
closed fibre is connected; finite-dimensionality makes it Artinian, hence
its prime spectrum is discrete and consists of one point.  The Jacobson
radical comparison for finite algebras then lifts uniqueness of the maximal
ideal to the original algebra.
-/

noncomputable section

open IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u v

/-- A nontrivial Artinian ring with connected prime spectrum is local. -/
theorem isLocalRing_of_isArtinianRing_of_connectedSpace_spec
    (Q : Type u) [CommRing Q] [IsArtinianRing Q] [Nontrivial Q]
    [ConnectedSpace (PrimeSpectrum Q)] :
    IsLocalRing Q := by
  have hsubsingleton : Subsingleton (PrimeSpectrum Q) := by
    constructor
    intro p q
    have hclopen : IsClopen ({p} : Set (PrimeSpectrum Q)) :=
      isClopen_discrete {p}
    rcases (connectedSpace_iff_clopen.mp
      (show ConnectedSpace (PrimeSpectrum Q) from inferInstance)).2
        {p} hclopen with hempty | huniv
    · exact False.elim (Set.singleton_ne_empty p hempty)
    · have hqp : q ∈ ({p} : Set (PrimeSpectrum Q)) := by
        rw [huniv]
        trivial
      exact (Set.mem_singleton_iff.mp hqp).symm
  obtain ⟨M, hM⟩ := Ideal.exists_maximal Q
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  let p : PrimeSpectrum Q := ⟨M, hM.isPrime⟩
  let q : PrimeSpectrum Q := ⟨N, hN.isPrime⟩
  exact (congrArg PrimeSpectrum.asIdeal
    (@Subsingleton.elim (PrimeSpectrum Q) hsubsingleton p q)).symm

/-- A finite domain algebra over a complete Noetherian local ring has a
unique maximal ideal. -/
theorem isLocalRing_of_finiteDomain_of_maximalAdicComplete
    {R C : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C] :
    IsLocalRing C := by
  let m : Ideal R := maximalIdeal R
  let J : Ideal C := m.map (algebraMap R C)
  let Q := C ⧸ J
  let q : C →+* Q := Ideal.Quotient.mk J
  have hJjac : J ≤ Ideal.jacobson (⊥ : Ideal C) :=
    (open _root_.ValuationTheory.DiscreteValuationField in
      ideal_map_le_jacobson_bot_of_le_jacobson_bot_of_moduleFinite
        (R := R) (S := C) (I := m))
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  have hJne : J ≠ ⊤ := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal C
    exact ne_top_of_le_ne_top hM.ne_top <|
      hJjac.trans (sInf_le ⟨bot_le, hM⟩)
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJne
  let : ConnectedSpace (PrimeSpectrum Q) := by
    change ConnectedSpace (Spec (.of Q))
    exact
      connectedSpace_spec_quotient_map_of_finiteDomain_of_maximalAdicComplete
        R m le_rfl
  let k := R ⧸ m
  let : Field k := Ideal.Quotient.field m
  let : Module.Finite R Q :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ R J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R J)
  let : Module.Finite k Q :=
    Module.Finite.of_restrictScalars_finite R k Q
  let : IsArtinianRing Q := IsArtinianRing.of_finite k Q
  let : IsLocalRing Q :=
    isLocalRing_of_isArtinianRing_of_connectedSpace_spec Q
  obtain ⟨M, hM⟩ := Ideal.exists_maximal C
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨M, hM, ?_⟩
  intro N hN
  have hJM : J ≤ M := hJjac.trans (sInf_le ⟨bot_le, hM⟩)
  have hJN : J ≤ N := hJjac.trans (sInf_le ⟨bot_le, hN⟩)
  have hqker : RingHom.ker q = J := Ideal.mk_ker
  have hkerM : RingHom.ker q ≤ M := by
    rw [hqker]
    exact hJM
  have hkerN : RingHom.ker q ≤ N := by
    rw [hqker]
    exact hJN
  let : M.IsMaximal := hM
  let : N.IsMaximal := hN
  have hmapM : (M.map q).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective hkerM
  have hmapN : (N.map q).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective hkerN
  have hmaps : M.map q = N.map q :=
    (IsLocalRing.maximal_ideal_unique Q).unique hmapM hmapN
  have hcomapM : (M.map q).comap q = M := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerM]
  have hcomapN : (N.map q).comap q = N := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkerN]
  rw [← hcomapM, ← hcomapN, hmaps]

/-- A faithfully integral finite domain over a complete normal local domain
has the same Krull dimension as the base. -/
theorem ringKrullDim_eq_of_finiteIntegralDomain_of_maximalAdicComplete
    {R C : Type u}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsAdicComplete (maximalIdeal R) R]
    [CommRing C] [IsDomain C] [Algebra R C] [Module.Finite R C]
    [Algebra.IsIntegral R C] [FaithfulSMul R C] :
    ringKrullDim C = ringKrullDim R := by
  let : IsLocalRing C :=
    isLocalRing_of_finiteDomain_of_maximalAdicComplete (R := R) (C := C)
  have hcomap :
      (maximalIdeal C).comap (algebraMap R C) = maximalIdeal R := by
    have hmax :
        ((maximalIdeal C).comap (algebraMap R C)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R C)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) (maximalIdeal C)
    exact (IsLocalRing.maximal_ideal_unique R).unique hmax
      (maximalIdeal.isMaximal R)
  have hmap :
      (maximalIdeal R).map (algebraMap R C) ≤ maximalIdeal C := by
    rw [Ideal.map_le_iff_le_comap, hcomap]
  calc
    ringKrullDim C =
        (((maximalIdeal C).height : ℕ∞) : WithBot ℕ∞) :=
      (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := C)).symm
    _ = ringKrullDim R :=
      prime_height_eq_ringKrullDim_of_map_maximalIdeal_le
        (R := R) (C := C) (maximalIdeal C) hmap

/-- The integral-closure algebra attached to a connected finite-etale cover
of a positive-dimensional punctured spectrum is local when the base is
complete. -/
theorem connectedPuncturedCover_integralClosure_isLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsLocalRing (integralClosure R W.left.functionField) := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let K : Type u := U.functionField
  let : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R L
  let : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  exact isLocalRing_of_finiteDomain_of_maximalAdicComplete
    (R := R) (C := C)

/-- The integral-closure algebra of a connected punctured cover has the same
Krull dimension as the complete normal local base. -/
theorem connectedPuncturedCover_integralClosure_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    [IsAdicComplete (maximalIdeal R) R]
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (W : FiniteEtale (Scheme.puncturedSpectrum R)) [IsConnected W] :
    let U := Scheme.puncturedSpectrum R
    letI : Nonempty U :=
      Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
    letI : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
      dsimp only [Scheme.puncturedSpectrumInclusion]
      infer_instance
    letI : IsIntegral U :=
      isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
    letI : Algebra R U.functionField :=
      puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
    letI : IsFractionRing R U.functionField :=
      puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra R W.left.functionField :=
      ((algebraMap U.functionField W.left.functionField).comp
        (algebraMap R U.functionField)).toAlgebra
    letI : IsScalarTower R U.functionField W.left.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    ringKrullDim (integralClosure R W.left.functionField) =
      ringKrullDim R := by
  dsimp only
  let U := Scheme.puncturedSpectrum R
  let : Nonempty U :=
    Scheme.puncturedSpectrum_nonempty_of_one_le_ringKrullDim R hpos
  let : IsOpenImmersion (Scheme.puncturedSpectrumInclusion R) := by
    dsimp only [Scheme.puncturedSpectrumInclusion]
    infer_instance
  let : IsIntegral U :=
    isIntegral_of_isOpenImmersion (Scheme.puncturedSpectrumInclusion R)
  let K : Type u := U.functionField
  let : Algebra R K :=
    puncturedSpectrumFunctionFieldAlgebraOfPositiveDimension R hpos
  let : IsFractionRing R K :=
    puncturedSpectrumFunctionField_isFractionRing_of_positiveDimension R hpos
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra R L :=
    ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let C := integralClosure R L
  let : Module.Finite R C :=
    connectedPuncturedCover_integralClosure_finite_of_positiveDimension
      R hpos W
  let : Algebra.IsIntegral R C := integralClosure.AlgebraIsIntegral
  let : FaithfulSMul R C :=
    integralClosure_faithfulSMul_of_fractionField
      (R := R) (K := K) (L := L)
  exact
    ringKrullDim_eq_of_finiteIntegralDomain_of_maximalAdicComplete
      (R := R) (C := C)

end AlgebraicGeometry.FiniteEtale

end
