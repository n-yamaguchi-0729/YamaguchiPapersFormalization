/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import EtaleFundamentalGroups.FiniteEtale.RegularSystem
import SchemeTheory.FiniteEtale.Henselian.PointedEtale

/-!
# Local etale algebras over a discrete valuation ring

An etale algebra which is local over a discrete valuation ring, with a local
structure map, is again a discrete valuation ring.  No module-finiteness of
the localized target is needed: finite presentation gives Noetherianity, and
the mapped uniformizer is a regular generator of the target maximal ideal.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe u v

/-- A Noetherian local, flat, formally unramified algebra over a discrete
valuation ring is a discrete valuation ring.  These are exactly the pieces
of etaleness used by the proof; this form remains applicable to arbitrary
prime localizations, whose map need not itself be presented as an `Etale`
instance. -/
theorem
    isDiscreteValuationRing_of_flat_of_formallyUnramified_of_isLocalHom
    {V : Type u} {C : Type v}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [Algebra V C] [IsLocalRing C]
    [IsNoetherianRing C] [Algebra.EssFiniteType V C] [Module.Flat V C]
    [Algebra.FormallyUnramified V C]
    [IsLocalHom (algebraMap V C)] :
    ∃ hdomainC : IsDomain C,
      letI : IsDomain C := hdomainC
      IsDiscreteValuationRing C := by
  obtain ⟨varpi, hvarpi⟩ := IsDiscreteValuationRing.exists_prime V
  have hvarpiRegular : IsSMulRegular V varpi := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    change varpi * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left hvarpi.ne_zero
  have hregular : IsRegular V [varpi] := by
    rw [isRegular_cons_iff]
    have hvarpiMem : varpi ∈ maximalIdeal V := by
      rw [mem_maximalIdeal]
      exact hvarpi.not_isUnit
    let : Nontrivial (QuotSMulTop varpi V) :=
      nontrivial_quotSMulTop_of_mem_maximalIdeal V hvarpiMem
    exact ⟨hvarpiRegular, IsRegular.nil V _⟩
  have hgenerate : Ideal.ofList [varpi] = maximalIdeal V := by
    rw [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq]
    exact hvarpi.irreducible.maximalIdeal_eq.symm
  let : Module.FaithfullyFlat V C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregularC : IsRegular C [algebraMap V C varpi] :=
    hregular.of_faithfullyFlat
  have hgenerateC : Ideal.ofList [algebraMap V C varpi] =
      maximalIdeal C := by
    calc
      Ideal.ofList [algebraMap V C varpi] =
          (Ideal.ofList [varpi]).map (algebraMap V C) := by
        simpa using
          (Ideal.map_ofList (algebraMap V C) [varpi]).symm
      _ = (maximalIdeal V).map (algebraMap V C) := by
        rw [hgenerate]
      _ = maximalIdeal C :=
        Algebra.FormallyUnramified.map_maximalIdeal
  have hdomainC : IsDomain C :=
    Kummer.isDomain_of_regularSystem
      [algebraMap V C varpi] hregularC hgenerateC
  let : IsDomain C := hdomainC
  have hvarpiImageNe : algebraMap V C varpi ≠ 0 :=
    by simpa using
      (FaithfulSMul.algebraMap_injective V C).ne hvarpi.ne_zero
  have hmaximalNe : maximalIdeal C ≠ ⊥ := by
    intro hbot
    apply hvarpiImageNe
    rw [← Ideal.mem_bot, ← hbot, ← hgenerateC]
    exact Ideal.subset_span (by simp)
  have hnotField : ¬ IsField C :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmaximalNe
  have hprincipal : (maximalIdeal C).IsPrincipal := by
    refine ⟨algebraMap V C varpi, ?_⟩
    simpa using hgenerateC.symm
  exact ⟨hdomainC,
    ((IsDiscreteValuationRing.TFAE C hnotField).out 5 1).mp hprincipal⟩

/-- A prime localization of an etale algebra over a discrete valuation ring
is a discrete valuation ring whenever the prime lies over the closed point.
The localized algebra need not be module-finite over the base. -/
theorem
    exists_isDiscreteValuationRing_localizationAtPrime_of_etale_liesOver_maximalIdeal
    {V : Type u} {E : Type v}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing E] [Algebra V E] [Algebra.Etale V E]
    (q : Ideal E) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal V)] :
    ∃ hdomain : IsDomain (Localization.AtPrime q),
      letI : IsDomain (Localization.AtPrime q) := hdomain
      IsDiscreteValuationRing (Localization.AtPrime q) := by
  let C := Localization.AtPrime q
  let : IsNoetherianRing E :=
    Algebra.FiniteType.isNoetherianRing V E
  let baseAlgebra : Algebra V C :=
    ((algebraMap E C).comp (algebraMap V E)).toAlgebra
  let : SMul V C := baseAlgebra.toSMul
  let : Algebra V C := baseAlgebra
  let : Module V C := baseAlgebra.toModule
  let : IsScalarTower V E C :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType V C :=
    Algebra.EssFiniteType.comp V E C
  let : Module.Flat V E := inferInstance
  let : Module.Flat E C := IsLocalization.flat C q.primeCompl
  let : Module.Flat V C := Module.Flat.trans V E C
  let : Algebra.FormallyUnramified V C :=
    Algebra.FormallyUnramified.comp V E C
  let : IsLocalHom (algebraMap V C) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
      (R := V) (S := E) q
  exact
    isDiscreteValuationRing_of_flat_of_formallyUnramified_of_isLocalHom
      (V := V) (C := C)

/-- A local etale algebra over a discrete valuation ring is a discrete
valuation ring.  No module-finiteness of the target is required. -/
theorem isDiscreteValuationRing_of_etale_of_isLocalHom
    {V : Type u} {C : Type v}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [Algebra V C] [IsLocalRing C]
    [Algebra.Etale V C] [IsLocalHom (algebraMap V C)] :
    ∃ hdomainC : IsDomain C,
      letI : IsDomain C := hdomainC
      IsDiscreteValuationRing C := by
  let : IsNoetherianRing C :=
    Algebra.FiniteType.isNoetherianRing V C
  exact
    isDiscreteValuationRing_of_flat_of_formallyUnramified_of_isLocalHom
      (V := V) (C := C)

end EtaleFundamentalGroups

end
