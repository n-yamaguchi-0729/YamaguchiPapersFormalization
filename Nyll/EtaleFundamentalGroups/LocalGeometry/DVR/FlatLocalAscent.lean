/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Regular.Flat
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# DVR ascent along a flat local map

A flat local map out of a discrete valuation ring is faithfully flat.  If
the source closed point generates the target closed point, the image of a
source uniformizer is therefore a one-element regular system of parameters
on the target.  For a Noetherian local target this produces its domain and
discrete-valuation-ring structures without assuming either one.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe uV uW

/-- A Noetherian local flat algebra over a DVR is a DVR when the mapped
source maximal ideal is the target maximal ideal.

Domainhood of the target is produced from the mapped one-element regular
system before the DVR criterion is applied; it is not a hypothesis. -/
theorem
    exists_isDomain_isDiscreteValuationRing_of_flat_local_of_map_maximalIdeal_eq
    {V : Type uV} {W : Type uW}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [Algebra V W] [IsLocalRing W] [IsNoetherianRing W]
    [Module.Flat V W] [IsLocalHom (algebraMap V W)]
    (hmax :
      (maximalIdeal V).map (algebraMap V W) = maximalIdeal W) :
    ∃ hdomainW : IsDomain W,
      letI : IsDomain W := hdomainW
      IsDiscreteValuationRing W := by
  obtain ⟨varpi, hvarpi⟩ := IsDiscreteValuationRing.exists_prime V
  have hvarpiRegular : IsSMulRegular V varpi := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    change varpi * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left hvarpi.ne_zero
  have hregularV : IsRegular V [varpi] := by
    rw [isRegular_cons_iff]
    have hvarpiMem : varpi ∈ maximalIdeal V := by
      rw [mem_maximalIdeal]
      exact hvarpi.not_isUnit
    let : Nontrivial (QuotSMulTop varpi V) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal V hvarpiMem
    exact ⟨hvarpiRegular, IsRegular.nil V _⟩
  have hgenerateV : Ideal.ofList [varpi] = maximalIdeal V := by
    rw [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq]
    exact hvarpi.irreducible.maximalIdeal_eq.symm
  let : Module.FaithfullyFlat V W :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregularW : IsRegular W [algebraMap V W varpi] :=
    hregularV.of_faithfullyFlat
  have hgenerateW : Ideal.ofList [algebraMap V W varpi] =
      maximalIdeal W := by
    calc
      Ideal.ofList [algebraMap V W varpi] =
          (Ideal.ofList [varpi]).map (algebraMap V W) := by
        simpa using
          (Ideal.map_ofList (algebraMap V W) [varpi]).symm
      _ = (maximalIdeal V).map (algebraMap V W) := by
        rw [hgenerateV]
      _ = maximalIdeal W := hmax
  have hdomainW : IsDomain W :=
    Kummer.isDomain_of_regularSystem
      [algebraMap V W varpi] hregularW hgenerateW
  let : IsDomain W := hdomainW
  have hvarpiImageNe : algebraMap V W varpi ≠ 0 := by
    simpa using
      (FaithfulSMul.algebraMap_injective V W).ne hvarpi.ne_zero
  have hmaximalNe : maximalIdeal W ≠ ⊥ := by
    intro hbot
    apply hvarpiImageNe
    rw [← Ideal.mem_bot, ← hbot, ← hgenerateW]
    exact Ideal.subset_span (by simp)
  have hnotField : ¬ IsField W :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmaximalNe
  have hprincipal : (maximalIdeal W).IsPrincipal := by
    refine ⟨algebraMap V W varpi, ?_⟩
    simpa using hgenerateW.symm
  exact ⟨hdomainW,
    ((IsDiscreteValuationRing.TFAE W hnotField).out 5 1).mp hprincipal⟩

end EtaleFundamentalGroups

end
