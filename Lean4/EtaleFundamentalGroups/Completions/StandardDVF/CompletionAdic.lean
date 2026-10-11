/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import EtaleFundamentalGroups.Completions.StandardDVF.Completion

/-!
# The standard valued completion realizes the adic completion of a DVR

Starting from a DVR `V` and a chosen fraction field `K`, this file compares
the `maximalIdeal V`-adic completion of `V` with the valuation subring in the
actual valued-field completion of the standard valuation on `K`.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Filter
open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations

universe uV uK

/-- The integer ring in the actual valued-field completion. -/
abbrev standardDVFCompletionValuationSubring
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] : Type uK :=
  (standardDVFCompletionCompleteDVF V K).valuationSubring

/-- The maximal ideal of the integer ring in the actual valued-field
completion. -/
abbrev standardDVFCompletionValuationSubringMaximalIdeal
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    Ideal (standardDVFCompletionValuationSubring V K) :=
  (standardDVFCompletionCompleteDVF V K).maximalIdeal

/-- The canonical map from the original DVR into the valuation subring of the
actual valued-field completion of its standard valuation. -/
noncomputable def standardDVRToCompletionValuationSubringMap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    V →+* (standardDVFCompletionCompleteDVF V K).valuationSubring := by
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  letI : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  letI : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  exact
    (algebraMap base.valuationSubring target.valuationSubring).comp
      e.toRingHom

/-- The `V`-algebra structure on the completed valuation subring induced by
the canonical DVR map. -/
@[reducible]
noncomputable def standardDVFCompletionValuationSubringAlgebra
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    Algebra V (standardDVFCompletionCompleteDVF V K).valuationSubring :=
  (standardDVRToCompletionValuationSubringMap V K).toAlgebra

/-- In the ambient completed field, the canonical DVR map is the original
fraction-field embedding followed by the valued completion map. -/
@[simp]
theorem coe_standardDVRToCompletionValuationSubringMap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (x : V) :
    ((standardDVRToCompletionValuationSubringMap V K x :
        (standardDVFCompletionCompleteDVF V K).valuationSubring) :
      standardDVFCompletionField V K) =
      standardDVFCompletionMap V K (algebraMap V K x) := by
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  change algebraMap K (standardDVFCompletionField V K)
      ((e x : base.valuationSubring) : K) =
    standardDVFCompletionMap V K (algebraMap V K x)
  rw [standardDVFCompletion_algebraMap_apply]
  rfl

/-- The source maximal ideal extends to the maximal ideal of the completed
valuation subring. -/
theorem standardDVRToCompletion_maximalIdeal_map_eq
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    Ideal.map (algebraMap V target.valuationSubring)
        (IsLocalRing.maximalIdeal V) =
      target.maximalIdeal := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  let g : base.valuationSubring →+* target.valuationSubring :=
    algebraMap base.valuationSubring target.valuationSubring
  calc
    Ideal.map (algebraMap V target.valuationSubring)
          (IsLocalRing.maximalIdeal V) =
        Ideal.map (g.comp e.toRingHom)
          (IsLocalRing.maximalIdeal V) := rfl
    _ = Ideal.map g
          (Ideal.map e.toRingHom (IsLocalRing.maximalIdeal V)) := by
      exact (Ideal.map_map e.toRingHom g).symm
    _ = Ideal.map g base.maximalIdeal :=
      congrArg (Ideal.map g)
        (IsLocalRing.map_ringEquiv_maximalIdeal e)
    _ = target.maximalIdeal :=
      standardDVFCompletion_maximalIdeal_map_eq V K

/-- The canonical map from a DVR to the valuation subring in its actual
valued-field completion is local. -/
theorem standardDVRToCompletion_isLocalHom
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    IsLocalHom (algebraMap V target.valuationSubring) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  have hmax : Ideal.map (algebraMap V target.valuationSubring)
      (IsLocalRing.maximalIdeal V) = target.maximalIdeal :=
    standardDVRToCompletion_maximalIdeal_map_eq V K
  exact ((IsLocalRing.local_hom_TFAE
    (algebraMap V target.valuationSubring)).out 3 1).mp hmax.le

/-- Contraction of every power of the completed maximal ideal is the
corresponding power of the original maximal ideal. -/
theorem standardDVRToCompletion_maximalIdeal_pow_comap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    (target.maximalIdeal ^ n).comap
        (algebraMap V target.valuationSubring) =
      IsLocalRing.maximalIdeal V ^ n := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : Module.FaithfullyFlat
      base.valuationSubring target.valuationSubring :=
    standardDVFCompletion_faithfullyFlat V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  let g : base.valuationSubring →+* target.valuationSubring :=
    algebraMap base.valuationSubring target.valuationSubring
  have hmap : Ideal.map g base.maximalIdeal = target.maximalIdeal :=
    standardDVFCompletion_maximalIdeal_map_eq V K
  have hemap :
      Ideal.map e.toRingHom (IsLocalRing.maximalIdeal V) =
        base.maximalIdeal :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  calc
    (target.maximalIdeal ^ n).comap
          (algebraMap V target.valuationSubring) =
        ((Ideal.map g (base.maximalIdeal ^ n)).comap g).comap
          e.toRingHom := by
      rw [Ideal.comap_comap, Ideal.map_pow, hmap]
      rfl
    _ = (base.maximalIdeal ^ n).comap e.toRingHom := by
      rw [Ideal.comap_map_eq_self_of_faithfullyFlat]
    _ = IsLocalRing.maximalIdeal V ^ n := by
      rw [← hemap, ← Ideal.map_pow]
      ext x
      change e x ∈
          Ideal.map e.toRingHom (IsLocalRing.maximalIdeal V ^ n) ↔
        x ∈ IsLocalRing.maximalIdeal V ^ n
      exact Ideal.apply_mem_of_equiv_iff

/-- Density of the original fraction field gives representatives modulo every
power of the maximal ideal in the completed valuation subring. -/
theorem standardDVRToCompletion_exists_approx_mod_maximalIdeal_pow
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (n : ℕ)
    (y : (standardDVFCompletionCompleteDVF V K).valuationSubring) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    ∃ x : V,
      algebraMap V target.valuationSubring x - y ∈
        target.maximalIdeal ^ n := by
  dsimp only
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  rcases base.exists_uniformizer with ⟨pi, hpi⟩
  let piHat : target.valuationSubring :=
    ValuedExtension.integerMap base target.toDVF pi
  have hpiHat : target.valuation.IsUniformizer
      (piHat : standardDVFCompletionField V K) := by
    change target.valuation.IsUniformizer
      (((ValuedExtension.integerMap base target.toDVF) pi :
        target.valuationSubring) : standardDVFCompletionField V K)
    rw [ValuedExtension.integerMap_apply,
      standardDVFCompletion_algebraMap_apply]
    exact standardDVFCompletionMap_isUniformizer V K pi hpi
  let radius : standardDVFCompletionField V K :=
    ((piHat ^ n : target.valuationSubring) :
      standardDVFCompletionField V K)
  have hradius_ne :
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))) radius ≠ 0 := by
    rw [← standardDVFCompletionCompleteDVF_valuation V K]
    change target.valuation
      ((piHat : standardDVFCompletionField V K) ^ n) ≠ 0
    rw [map_pow]
    exact pow_ne_zero n hpiHat.val_ne_zero
  have hrestrict_radius_ne :
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).restrict radius ≠ 0 := by
    simpa using hradius_ne
  let s : Set (standardDVFCompletionField V K) :=
    {z | (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ)))
        (z - (y : standardDVFCompletionField V K)) <
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))) radius}
  have hs : s ∈ nhds (y : standardDVFCompletionField V K) := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0
      ((Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).restrict radius)
      hrestrict_radius_ne, ?_⟩
    intro z hz
    change (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).restrict
          (z - (y : standardDVFCompletionField V K)) <
        (Units.mk0
          ((Valued.v : Valuation (standardDVFCompletionField V K)
            (WithZero (Multiplicative ℤ))).restrict radius)
          hrestrict_radius_ne).1 at hz
    change (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ)))
          (z - (y : standardDVFCompletionField V K)) <
        (Valued.v : Valuation (standardDVFCompletionField V K)
          (WithZero (Multiplicative ℤ))) radius
    rw [Valuation.restrict_lt_iff_lt_embedding] at hz
    simpa using hz
  rcases UniformSpace.Completion.denseRange_coe.mem_nhds hs with
    ⟨a, ha⟩
  have ha_lt : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ)))
      ((a : standardDVFCompletionField V K) -
        (y : standardDVFCompletionField V K)) <
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))) radius := ha
  have hradius_le_one :
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))) radius ≤ 1 := by
    rw [← standardDVFCompletionCompleteDVF_valuation V K]
    change target.valuation
      ((piHat : standardDVFCompletionField V K) ^ n) ≤ 1
    rw [map_pow]
    exact pow_le_one₀ zero_le hpiHat.val_lt_one.le
  have ha_le : WithVal.valuation v a ≤ 1 := by
    have hy_le : (Valued.v : Valuation
        (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ)))
        (y : standardDVFCompletionField V K) ≤ 1 := by
      rw [← standardDVFCompletionCompleteDVF_valuation V K]
      exact y.2
    have hdiff_le_one : (Valued.v : Valuation
        (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ)))
        ((a : standardDVFCompletionField V K) -
          (y : standardDVFCompletionField V K)) ≤ 1 :=
      ha_lt.le.trans hradius_le_one
    have hsum_le : (Valued.v : Valuation
        (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ)))
        (a : standardDVFCompletionField V K) ≤ 1 := by
      calc
        (Valued.v : Valuation (standardDVFCompletionField V K)
            (WithZero (Multiplicative ℤ)))
              (a : standardDVFCompletionField V K) =
            (Valued.v : Valuation (standardDVFCompletionField V K)
              (WithZero (Multiplicative ℤ)))
              (((a : standardDVFCompletionField V K) -
                  (y : standardDVFCompletionField V K)) +
                (y : standardDVFCompletionField V K)) := by
          ring_nf
        _ ≤ max
              ((Valued.v : Valuation (standardDVFCompletionField V K)
                (WithZero (Multiplicative ℤ)))
                ((a : standardDVFCompletionField V K) -
                  (y : standardDVFCompletionField V K)))
              ((Valued.v : Valuation (standardDVFCompletionField V K)
                (WithZero (Multiplicative ℤ)))
                (y : standardDVFCompletionField V K)) :=
          (Valued.v : Valuation (standardDVFCompletionField V K)
            (WithZero (Multiplicative ℤ))).map_add _ _
        _ ≤ 1 := max_le hdiff_le_one hy_le
    have hva : (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ)))
        ((a : WithVal v) : standardDVFCompletionField V K) =
        WithVal.valuation v a := by
      exact Valued.valuedCompletion_apply (x := a)
    simpa only [hva] using hsum_le
  let xK : K := WithVal.equiv v a
  have hxK : v xK ≤ 1 := by
    change v (WithVal.equiv v a) ≤ 1
    simpa [WithVal.equiv_apply,
      WithVal.valuation_apply_eq_ofVal] using ha_le
  let xBase : base.valuationSubring := ⟨xK, hxK⟩
  let x : V := e.symm xBase
  have hmap :
      (((algebraMap V target.valuationSubring x :
          target.valuationSubring) :
        standardDVFCompletionField V K)) =
        (a : standardDVFCompletionField V K) := by
    change
      ((standardDVRToCompletionValuationSubringMap V K x :
          target.valuationSubring) : standardDVFCompletionField V K) =
        (a : standardDVFCompletionField V K)
    rw [coe_standardDVRToCompletionValuationSubringMap]
    change standardDVFCompletionMap V K
        (algebraMap V K (e.symm xBase)) =
      (a : standardDVFCompletionField V K)
    have hxBase : algebraMap V K (e.symm xBase) =
        (xBase : K) := by
      change (((e (e.symm xBase) : base.valuationSubring) : K)) =
        (xBase : K)
      rw [RingEquiv.apply_symm_apply]
    rw [hxBase]
    rfl
  refine ⟨x, ?_⟩
  rw [Valuation.mem_maximalIdeal_pow_iff_valuation_le_uniformizer_pow
    (val := target.valuation) (pi := piHat) (hpi := hpiHat) (n := n)]
  change target.valuation
      (((algebraMap V target.valuationSubring x :
          target.valuationSubring) : standardDVFCompletionField V K) -
        (y : standardDVFCompletionField V K)) ≤
    target.valuation
      ((piHat : standardDVFCompletionField V K) ^ n)
  rw [standardDVFCompletionCompleteDVF_valuation, hmap]
  exact ha_lt.le

/-- The map on the `n`-th finite quotients induced by the canonical DVR map. -/
noncomputable def standardDVRCompletionPowQuotientAlgHom
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    (V ⧸ (IsLocalRing.maximalIdeal V ^ n)) →ₐ[V]
      (target.valuationSubring ⧸ (target.maximalIdeal ^ n)) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  letI : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  exact Ideal.quotientMapₐ (target.maximalIdeal ^ n)
    (Algebra.ofId V target.valuationSubring) (by
      change IsLocalRing.maximalIdeal V ^ n ≤
        (target.maximalIdeal ^ n).comap
          (algebraMap V target.valuationSubring)
      rw [standardDVRToCompletion_maximalIdeal_pow_comap V K n])

@[simp]
theorem standardDVRCompletionPowQuotientAlgHom_apply_mk
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (n : ℕ) (x : V) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    standardDVRCompletionPowQuotientAlgHom V K n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x) =
      Ideal.Quotient.mk (target.maximalIdeal ^ n)
        (algebraMap V target.valuationSubring x) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  change (Ideal.quotientMapₐ (target.maximalIdeal ^ n)
      (Algebra.ofId V target.valuationSubring) _)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x) =
    Ideal.Quotient.mk (target.maximalIdeal ^ n)
      (algebraMap V target.valuationSubring x)
  rw [Ideal.quotient_map_mkₐ]
  rfl

/-- The finite quotient map is injective because all powers of the target
maximal ideal contract to the corresponding source powers. -/
theorem standardDVRCompletionPowQuotientAlgHom_injective
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    Function.Injective (standardDVRCompletionPowQuotientAlgHom V K n) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  intro a b hab
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [standardDVRCompletionPowQuotientAlgHom_apply_mk,
    standardDVRCompletionPowQuotientAlgHom_apply_mk,
    Ideal.Quotient.eq] at hab
  rw [Ideal.Quotient.eq]
  have hab' : algebraMap V target.valuationSubring (x - y) ∈
      target.maximalIdeal ^ n := by
    simpa using hab
  have hab'' : x - y ∈ (target.maximalIdeal ^ n).comap
      (algebraMap V target.valuationSubring) := hab'
  rwa [standardDVRToCompletion_maximalIdeal_pow_comap V K n] at hab''

/-- The finite quotient map is surjective by approximation in the actual
valued-field completion. -/
theorem standardDVRCompletionPowQuotientAlgHom_surjective
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    Function.Surjective (standardDVRCompletionPowQuotientAlgHom V K n) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  intro q
  induction q using Quotient.inductionOn' with
  | _ y =>
      rcases standardDVRToCompletion_exists_approx_mod_maximalIdeal_pow
        V K n y with ⟨x, hx⟩
      refine ⟨Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal V ^ n) x, ?_⟩
      change standardDVRCompletionPowQuotientAlgHom V K n
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x) =
        Ideal.Quotient.mk (target.maximalIdeal ^ n) y
      rw [standardDVRCompletionPowQuotientAlgHom_apply_mk]
      exact Ideal.Quotient.eq.mpr hx

/-- Every finite maximal-ideal-power quotient of the original DVR is
canonically identified with the corresponding quotient of the completed
valuation subring. -/
noncomputable def standardDVRCompletionPowQuotientAlgEquiv
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (n : ℕ) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    (V ⧸ (IsLocalRing.maximalIdeal V ^ n)) ≃ₐ[V]
      (target.valuationSubring ⧸ (target.maximalIdeal ^ n)) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  letI : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  exact AlgEquiv.ofBijective
    (standardDVRCompletionPowQuotientAlgHom V K n)
    ⟨standardDVRCompletionPowQuotientAlgHom_injective V K n,
      standardDVRCompletionPowQuotientAlgHom_surjective V K n⟩

@[simp]
theorem standardDVRCompletionPowQuotientAlgEquiv_apply_mk
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (n : ℕ) (x : V) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    standardDVRCompletionPowQuotientAlgEquiv V K n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x) =
      Ideal.Quotient.mk (target.maximalIdeal ^ n)
        (algebraMap V target.valuationSubring x) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  change standardDVRCompletionPowQuotientAlgHom V K n
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x) =
    Ideal.Quotient.mk (target.maximalIdeal ^ n)
      (algebraMap V target.valuationSubring x)
  exact standardDVRCompletionPowQuotientAlgHom_apply_mk V K n x

/-- Naturality of the finite quotient equivalences under the power transition
maps. -/
theorem standardDVRCompletionPowQuotientAlgEquiv_factorPow
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    {m n : ℕ} (hmn : m ≤ n)
    (x : V ⧸ (IsLocalRing.maximalIdeal V ^ n)) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    Ideal.Quotient.factorPow target.maximalIdeal hmn
        (standardDVRCompletionPowQuotientAlgEquiv V K n x) =
      standardDVRCompletionPowQuotientAlgEquiv V K m
        (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal V) hmn x) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  induction x using Quotient.inductionOn' with
  | _ x =>
      change Ideal.Quotient.factorPow target.maximalIdeal hmn
          (standardDVRCompletionPowQuotientAlgEquiv V K n
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x)) =
        standardDVRCompletionPowQuotientAlgEquiv V K m
          (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal V) hmn
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ n) x))
      rw [standardDVRCompletionPowQuotientAlgEquiv_apply_mk,
        Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
        standardDVRCompletionPowQuotientAlgEquiv_apply_mk]

/-- Naturality of the inverse finite quotient equivalences. -/
theorem standardDVRCompletionPowQuotientAlgEquiv_symm_factorPow
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    {m n : ℕ} (hmn : m ≤ n) :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    ∀ x : target.valuationSubring ⧸ (target.maximalIdeal ^ n),
      Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal V) hmn
          ((standardDVRCompletionPowQuotientAlgEquiv V K n).symm x) =
        (standardDVRCompletionPowQuotientAlgEquiv V K m).symm
          (Ideal.Quotient.factorPow target.maximalIdeal hmn x) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra V target.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  intro x
  apply (standardDVRCompletionPowQuotientAlgEquiv V K m).injective
  rw [AlgEquiv.apply_symm_apply,
    ← standardDVRCompletionPowQuotientAlgEquiv_factorPow V K hmn
      ((standardDVRCompletionPowQuotientAlgEquiv V K n).symm x),
    AlgEquiv.apply_symm_apply]

section InverseLimit

variable (V : Type uV) (K : Type uK)
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [Field K] [Algebra V K] [IsFractionRing V K]

local notation "I_V" => IsLocalRing.maximalIdeal V
local notation "V_hat" => standardDVFCompletionValuationSubring V K
local notation "I_hat" =>
  standardDVFCompletionValuationSubringMaximalIdeal V K

local instance completionValuationSubringAlgebra : Algebra V V_hat :=
  standardDVFCompletionValuationSubringAlgebra V K

private theorem factorPow_evalₐ
    {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ I n x)
  have hn : AdicCompletion.eval I R n x =
      Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval I x (by simp), ← ha,
      Ideal.Quotient.factor_mk]
  have hm : AdicCompletion.eval I R m x =
      Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a := by
    calc
      AdicCompletion.eval I R m x =
          AdicCompletion.transitionMap I R hmn
            (AdicCompletion.eval I R n x) :=
        (AdicCompletion.transitionMap_comp_eval_apply I R hmn x).symm
      _ = Ideal.Quotient.mk (I ^ m • ⊤ : Ideal R) a := by
        rw [hn]
        rfl
  calc
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
        Ideal.Quotient.mk (I ^ m) a := by
      rw [← ha, Ideal.Quotient.factor_mk]
    _ = AdicCompletion.evalₐ I m x := by
      rw [← AdicCompletion.factor_eval_eq_evalₐ I x (by simp), hm]
      rfl

private noncomputable def completionToValuationSubringQuotientRingHom
    (n : ℕ) :
    AdicCompletion I_V V →+* V_hat ⧸ (I_hat ^ n) :=
  (standardDVRCompletionPowQuotientAlgEquiv V K n).toRingEquiv.toRingHom.comp
    (AdicCompletion.evalₐ I_V n).toRingHom

private theorem completionToValuationSubringQuotientRingHom_compatible :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I_hat hmn).comp
          (completionToValuationSubringQuotientRingHom V K n) =
        completionToValuationSubringQuotientRingHom V K m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow I_hat hmn
      (standardDVRCompletionPowQuotientAlgEquiv V K n
        (AdicCompletion.evalₐ I_V n x)) =
    standardDVRCompletionPowQuotientAlgEquiv V K m
      (AdicCompletion.evalₐ I_V m x)
  rw [standardDVRCompletionPowQuotientAlgEquiv_factorPow V K hmn,
    factorPow_evalₐ I_V hmn]

private noncomputable def completionToValuationSubringCompletionRingHom :
    AdicCompletion I_V V →+* AdicCompletion I_hat V_hat :=
  AdicCompletion.liftRingHom I_hat
    (completionToValuationSubringQuotientRingHom V K)
    (completionToValuationSubringQuotientRingHom_compatible V K)

@[simp]
private theorem evalₐ_completionToValuationSubringCompletionRingHom
    (n : ℕ) (x : AdicCompletion I_V V) :
    AdicCompletion.evalₐ I_hat n
        (completionToValuationSubringCompletionRingHom V K x) =
      standardDVRCompletionPowQuotientAlgEquiv V K n
        (AdicCompletion.evalₐ I_V n x) := by
  unfold completionToValuationSubringCompletionRingHom
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private noncomputable def valuationSubringCompletionToQuotientRingHom
    (n : ℕ) :
    AdicCompletion I_hat V_hat →+* V ⧸ (I_V ^ n) :=
  (standardDVRCompletionPowQuotientAlgEquiv V K n).symm.toRingEquiv.toRingHom.comp
    (AdicCompletion.evalₐ I_hat n).toRingHom

private theorem valuationSubringCompletionToQuotientRingHom_compatible :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I_V hmn).comp
          (valuationSubringCompletionToQuotientRingHom V K n) =
        valuationSubringCompletionToQuotientRingHom V K m := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow I_V hmn
      ((standardDVRCompletionPowQuotientAlgEquiv V K n).symm
        (AdicCompletion.evalₐ I_hat n x)) =
    (standardDVRCompletionPowQuotientAlgEquiv V K m).symm
      (AdicCompletion.evalₐ I_hat m x)
  rw [standardDVRCompletionPowQuotientAlgEquiv_symm_factorPow V K hmn,
    factorPow_evalₐ I_hat hmn]

private noncomputable def valuationSubringCompletionToCompletionRingHom :
    AdicCompletion I_hat V_hat →+* AdicCompletion I_V V :=
  AdicCompletion.liftRingHom I_V
    (valuationSubringCompletionToQuotientRingHom V K)
    (valuationSubringCompletionToQuotientRingHom_compatible V K)

@[simp]
private theorem evalₐ_valuationSubringCompletionToCompletionRingHom
    (n : ℕ) (x : AdicCompletion I_hat V_hat) :
    AdicCompletion.evalₐ I_V n
        (valuationSubringCompletionToCompletionRingHom V K x) =
      (standardDVRCompletionPowQuotientAlgEquiv V K n).symm
        (AdicCompletion.evalₐ I_hat n x) := by
  unfold valuationSubringCompletionToCompletionRingHom
  rw [AdicCompletion.evalₐ_liftRingHom]
  rfl

private theorem completionToValuationSubring_comp_fromValuationSubring :
    (completionToValuationSubringCompletionRingHom V K).comp
        (valuationSubringCompletionToCompletionRingHom V K) =
      RingHom.id (AdicCompletion I_hat V_hat) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

private theorem valuationSubringToCompletion_comp_fromCompletion :
    (valuationSubringCompletionToCompletionRingHom V K).comp
        (completionToValuationSubringCompletionRingHom V K) =
      RingHom.id (AdicCompletion I_V V) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

/-- Inverse-limit lift of the finite quotient equivalences between the
original DVR and the valuation subring in its actual valued completion. -/
noncomputable def standardDVRAdicCompletionEquivValuationSubringCompletion :
    AdicCompletion I_V V ≃ₐ[V] AdicCompletion I_hat V_hat :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom
      (completionToValuationSubringCompletionRingHom V K)
      (valuationSubringCompletionToCompletionRingHom V K)
      (completionToValuationSubring_comp_fromValuationSubring V K)
      (valuationSubringToCompletion_comp_fromCompletion V K)) (fun x => by
        apply AdicCompletion.ext_evalₐ
        intro n
        simp [AdicCompletion.algebraMap_apply])

@[simp]
theorem evalₐ_standardDVRAdicCompletionEquivValuationSubringCompletion
    (n : ℕ) (x : AdicCompletion I_V V) :
    AdicCompletion.evalₐ I_hat n
        (standardDVRAdicCompletionEquivValuationSubringCompletion V K x) =
      standardDVRCompletionPowQuotientAlgEquiv V K n
        (AdicCompletion.evalₐ I_V n x) :=
  evalₐ_completionToValuationSubringCompletionRingHom V K n x

local instance completionValuationSubringIsAdicComplete :
    IsAdicComplete I_hat V_hat :=
  (standardDVFCompletionCompleteDVF V K).isAdicComplete

private noncomputable def valuationSubringCompletionEquivSelf :
    AdicCompletion I_hat V_hat ≃ₐ[V] V_hat :=
  AlgEquiv.ofRingEquiv
    (f := (AdicCompletion.ofAlgEquiv I_hat).symm.toRingEquiv) (fun x => by
      change (AdicCompletion.ofAlgEquiv I_hat).symm
          (algebraMap V (AdicCompletion I_hat V_hat) x) =
        algebraMap V V_hat x
      rw [AdicCompletion.algebraMap_apply,
        AdicCompletion.ofAlgEquiv_symm_of])

/-- The valuation subring in the actual standard valued-field completion is
the `maximalIdeal V`-adic completion of the original DVR, canonically as a
`V`-algebra. -/
noncomputable def standardDVRAdicCompletionEquivCompletionValuationSubring :
    AdicCompletion I_V V ≃ₐ[V] V_hat :=
  (standardDVRAdicCompletionEquivValuationSubringCompletion V K).trans
    (valuationSubringCompletionEquivSelf V K)

@[simp]
theorem standardDVRAdicCompletionEquivCompletionValuationSubring_apply_of
    (x : V) :
    standardDVRAdicCompletionEquivCompletionValuationSubring V K
        (AdicCompletion.of I_V V x) =
      algebraMap V V_hat x :=
  (standardDVRAdicCompletionEquivCompletionValuationSubring V K).commutes x

/-- The canonical DVR map into the valuation subring of its actual completion
induces a bijection on residue fields. -/
theorem standardDVRToCompletion_residueFieldMap_bijective :
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra V target.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : IsLocalHom (algebraMap V target.valuationSubring) :=
      standardDVRToCompletion_isLocalHom V K
    Function.Bijective
      (IsLocalRing.ResidueField.map
        (algebraMap V target.valuationSubring)) := by
  dsimp only
  let target := standardDVFCompletionCompleteDVF V K
  let T := target.valuationSubring
  let : Algebra V T :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V T) :=
    standardDVRToCompletion_isLocalHom V K
  constructor
  · exact RingHom.injective _
  · intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    let e₀ := standardDVRCompletionPowQuotientAlgEquiv V K 1
    obtain ⟨x, hx⟩ := e₀.surjective
      (Ideal.Quotient.mk (target.maximalIdeal ^ 1) y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨IsLocalRing.residue V a, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    change Ideal.Quotient.mk target.maximalIdeal
        (algebraMap V T a) = Ideal.Quotient.mk target.maximalIdeal y
    have hx' : Ideal.Quotient.mk (target.maximalIdeal ^ 1)
          (algebraMap V T a) =
        Ideal.Quotient.mk (target.maximalIdeal ^ 1) y := by
      simpa only [e₀,
        standardDVRCompletionPowQuotientAlgEquiv_apply_mk] using hx
    exact Ideal.Quotient.eq.mpr <| by
      simpa only [pow_one] using Ideal.Quotient.eq.mp hx'

@[simp]
theorem quotient_mk_standardDVRAdicCompletionEquivCompletionValuationSubring
    (n : ℕ) (x : AdicCompletion I_V V) :
    Ideal.Quotient.mk (I_hat ^ n)
        (standardDVRAdicCompletionEquivCompletionValuationSubring V K x) =
      standardDVRCompletionPowQuotientAlgEquiv V K n
        (AdicCompletion.evalₐ I_V n x) := by
  change Ideal.Quotient.mk (I_hat ^ n)
      ((AdicCompletion.ofAlgEquiv I_hat).symm
        (standardDVRAdicCompletionEquivValuationSubringCompletion V K x)) = _
  rw [AdicCompletion.mk_ofAlgEquiv_symm,
    evalₐ_standardDVRAdicCompletionEquivValuationSubringCompletion]

end InverseLimit

end EtaleFundamentalGroups

end
