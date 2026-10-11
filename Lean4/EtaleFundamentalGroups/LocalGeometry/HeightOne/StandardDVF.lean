/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.RamificationInertia.Ramification
import ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions

/-!
# The standard discrete valuation field attached to a DVR

A discrete valuation ring inside a chosen fraction field determines the adic
rank-one discrete valuation of that field.  This file packages that valuation
as a `DVF`, transports a local map of DVRs to an extension of the packaged
valuations, and compares the resulting `DVF` ramification index with the
original ideal-theoretic ramification index.
-/

noncomputable section

namespace EtaleFundamentalGroups

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uW uK uL

/-- The rank-one discrete valuation field canonically attached to a DVR and a
chosen fraction field. -/
noncomputable def standardDVFOfDVR
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    DVF.{uK, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := (IsDiscreteValuationRing.maximalIdeal V).valuation K

/-- A local map between valuation subrings which agrees with the ambient
field map determines an extension of the two valuations. -/
private theorem valuation_hasExtension_of_local_valuationSubring_map
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    (f : base.valuationSubring →+* target.valuationSubring)
    [IsLocalHom f]
    (hcoe : ∀ z : base.valuationSubring,
      ((f z : target.valuationSubring) : L) =
        algebraMap K L (z : K)) :
    base.valuation.HasExtension target.valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext z
  change
    algebraMap K L z ∈ target.valuation.valuationSubring ↔
      z ∈ base.valuation.valuationSubring
  constructor
  · intro hzTarget
    by_contra hzBase
    have hz_ne : z ≠ 0 := by
      intro hz
      subst z
      exact hzBase base.valuation.valuationSubring.zero_mem
    have hinvNonunit :
        z⁻¹ ∈ base.valuation.valuationSubring.nonunits :=
      (base.valuation.valuationSubring.inv_mem_nonunits_iff).2
        (Or.inr hzBase)
    let zinverse : base.valuationSubring :=
      ⟨z⁻¹, base.valuation.valuationSubring.nonunits_subset hinvNonunit⟩
    have hzinverseMaximal :
        zinverse ∈ IsLocalRing.maximalIdeal base.valuationSubring := by
      apply base.valuation.valuationSubring.coe_mem_nonunits_iff.mp
      exact hinvNonunit
    have hmapMaximal :
        f zinverse ∈ IsLocalRing.maximalIdeal target.valuationSubring :=
      map_nonunit f zinverse hzinverseMaximal
    let ztarget : target.valuationSubring :=
      ⟨algebraMap K L z, hzTarget⟩
    have hproduct : f zinverse * ztarget = 1 := by
      apply Subtype.ext
      change
        ((f zinverse : target.valuationSubring) : L) *
            algebraMap K L z =
          1
      rw [hcoe]
      change algebraMap K L (z⁻¹) * algebraMap K L z = 1
      rw [← map_mul, inv_mul_cancel₀ hz_ne, map_one]
    have hone :
        (1 : target.valuationSubring) ∈
          IsLocalRing.maximalIdeal target.valuationSubring := by
      rw [← hproduct]
      exact
        (IsLocalRing.maximalIdeal target.valuationSubring).mul_mem_right
          ztarget hmapMaximal
    exact
      (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).isPrime.one_notMem
        hone
  · intro hzBase
    let zbase : base.valuationSubring := ⟨z, hzBase⟩
    have hzMap :
        ((f zbase : target.valuationSubring) : L) ∈
          target.valuation.valuationSubring :=
      (f zbase).property
    rwa [hcoe] at hzMap

/-- A local map of DVRs which induces the prescribed map of fraction fields
produces an extension between their standard rank-one discrete valuations. -/
theorem standardDVFOfDVR_hasExtension
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra K L]
    (f : V →+* W) [IsLocalHom f]
    (hcomm : (algebraMap W L).comp f =
      (algebraMap K L).comp (algebraMap V K)) :
    (standardDVFOfDVR V K).valuation.HasExtension
      (standardDVFOfDVR W L).valuation := by
  let base := standardDVFOfDVR V K
  let target := standardDVFOfDVR W L
  let eV : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  let eW : W ≃+* target.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := L)
  let f' : base.valuationSubring →+* target.valuationSubring :=
    eW.toRingHom.comp (f.comp eV.symm.toRingHom)
  let : IsLocalHom eV.symm.toRingHom :=
    IsLocalHom.of_surjective eV.symm.toRingHom eV.symm.surjective
  let : IsLocalHom eW.toRingHom :=
    IsLocalHom.of_surjective eW.toRingHom eW.surjective
  let : IsLocalHom (f.comp eV.symm.toRingHom) :=
    RingHom.isLocalHom_comp f eV.symm.toRingHom
  let : IsLocalHom f' :=
    RingHom.isLocalHom_comp eW.toRingHom (f.comp eV.symm.toRingHom)
  apply valuation_hasExtension_of_local_valuationSubring_map base target f'
  intro z
  change
    (((eW (f (eV.symm z)) : target.valuationSubring) : L)) =
      algebraMap K L (z : K)
  change algebraMap W L (f (eV.symm z)) = algebraMap K L (z : K)
  have hzcomm := DFunLike.congr_fun hcomm (eV.symm z)
  change algebraMap W L (f (eV.symm z)) =
    algebraMap K L (algebraMap V K (eV.symm z)) at hzcomm
  rw [hzcomm]
  congr 1
  change
    (((eV (eV.symm z) : base.valuationSubring) : K)) = (z : K)
  rw [RingEquiv.apply_symm_apply]

/-- A ring equivalence carries the maximal ideal of one local ring to the
maximal ideal of the other. -/
private theorem map_maximalIdeal_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
  ext y
  rw [Ideal.mem_map_of_equiv e y]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hy
    exact hx (by simpa using hy.map (e.symm : S →+* R))
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hx
    exact hy (by simpa using hx.map (e : R →+* S))

/-- Ramification indices agree when the two source ideals have the same image
in the target ring. -/
private theorem ramificationIdx'_eq_of_map_eq
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S]
    (f : R →+* S) (g : R' →+* S)
    (p : Ideal R) (q : Ideal R') (P : Ideal S)
    (h : Ideal.map f p = Ideal.map g q) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R' S := g.toAlgebra
    Ideal.ramificationIdx' p P = Ideal.ramificationIdx' q P := by
  unfold Ideal.ramificationIdx'
  change sSup {n | Ideal.map f p ≤ P ^ n} =
    sSup {n | Ideal.map g q ≤ P ^ n}
  rw [h]

/-- The ramification index of the standard `DVF` packages is the
ideal-theoretic ramification index of the original local map of DVRs. -/
theorem standardDVFOfDVR_ramificationIndex_eq_ramificationIdx
    {V : Type uV} {W : Type uW} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra W L] [IsFractionRing W L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra V W] [IsLocalHom (algebraMap V W)]
    (hcomm : (algebraMap W L).comp (algebraMap V W) =
      (algebraMap K L).comp (algebraMap V K)) :
    let base := standardDVFOfDVR V K
    let target := standardDVFOfDVR W L
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
    ramificationIndex base target =
      (IsLocalRing.maximalIdeal W).ramificationIdx V := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFOfDVR W L
  let hExt : base.valuation.HasExtension target.valuation :=
    standardDVFOfDVR_hasExtension (algebraMap V W) hcomm
  let : base.valuation.HasExtension target.valuation := hExt
  let eV : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  let eW : W ≃+* target.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := L)
  let iCan : base.valuationSubring →+* target.valuationSubring :=
    algebraMap base.valuationSubring target.valuationSubring
  let g : V →+* target.valuationSubring := iCan.comp eV.toRingHom
  let : Algebra V target.valuationSubring := g.toAlgebra
  let eWAlg : W ≃ₐ[V] target.valuationSubring :=
    AlgEquiv.ofRingEquiv (f := eW) (by
      intro a
      apply Subtype.ext
      change algebraMap W L (algebraMap V W a) =
        algebraMap K L (algebraMap V K a)
      exact DFunLike.congr_fun hcomm a)
  have htransport :=
    Ideal.ramificationIdx'_map_eq
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) eWAlg
  change Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
        (Ideal.map eW (IsLocalRing.maximalIdeal W)) =
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
        (IsLocalRing.maximalIdeal W) at htransport
  have hMaxW : Ideal.map eW (IsLocalRing.maximalIdeal W) =
      target.maximalIdeal :=
    map_maximalIdeal_ringEquiv eW
  rw [hMaxW] at htransport
  have hMaxV : Ideal.map eV (IsLocalRing.maximalIdeal V) =
      base.maximalIdeal :=
    map_maximalIdeal_ringEquiv eV
  have hMap : Ideal.map g (IsLocalRing.maximalIdeal V) =
      Ideal.map iCan base.maximalIdeal := by
    calc
      Ideal.map g (IsLocalRing.maximalIdeal V) =
          Ideal.map (iCan.comp eV.toRingHom)
            (IsLocalRing.maximalIdeal V) := rfl
      _ = Ideal.map iCan
            (Ideal.map eV (IsLocalRing.maximalIdeal V)) := by
            exact (Ideal.map_map eV.toRingHom iCan).symm
      _ = Ideal.map iCan base.maximalIdeal := by rw [hMaxV]
  have hOld :
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
          (IsLocalRing.maximalIdeal W) =
        ramificationIndex base target := by
    calc
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
          (IsLocalRing.maximalIdeal W) =
          Ideal.ramificationIdx' (IsLocalRing.maximalIdeal V)
            target.maximalIdeal := htransport.symm
      _ = Ideal.ramificationIdx' base.maximalIdeal target.maximalIdeal :=
        ramificationIdx'_eq_of_map_eq g iCan
          (IsLocalRing.maximalIdeal V) base.maximalIdeal
          target.maximalIdeal hMap
      _ = ramificationIndex base target := rfl
  have hf : Function.Injective (algebraMap V W) := by
    intro a b hab
    apply IsFractionRing.injective V K
    apply (algebraMap K L).injective
    have ha := DFunLike.congr_fun hcomm a
    have hb := DFunLike.congr_fun hcomm b
    change algebraMap W L (algebraMap V W a) =
      algebraMap K L (algebraMap V K a) at ha
    change algebraMap W L (algebraMap V W b) =
      algebraMap K L (algebraMap V K b) at hb
    exact ha.symm.trans ((congrArg (algebraMap W L) hab).trans hb)
  have hMaxVNe : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField V)
  have hMapMaxNe :
      Ideal.map (algebraMap V W) (IsLocalRing.maximalIdeal V) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hf).not.mpr hMaxVNe
  let : (IsLocalRing.maximalIdeal W).LiesOver
      (IsLocalRing.maximalIdeal V) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap V W)).symm⟩
  let : (IsLocalRing.maximalIdeal W).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal W).isPrime
  let : IsDedekindDomain W := inferInstance
  rw [← hOld]
  exact Ideal.ramificationIdx'_eq_ramificationIdx'
    (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W) hMapMaxNe

end EtaleFundamentalGroups

end
