/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.LocalGeometry.Regular.PairPrimeDichotomy

/-!
# Parameter quotients of a completed regular pair

For a regular parameter pair generating the closed point, the quotient of
the maximal-adic completion by either completed parameter is a DVR.  This
file records the second-parameter form needed by the iterated power-series
presentation of the completion.  It also identifies the quotient maximal
ideal with the image of the first parameter and proves surjectivity of the
canonical map from the source ring to the final residue field.

All three facts are generated from the regular pair and the canonical
maximal-adic completion map; no Noetherian hypothesis on the completion is
used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence

universe u

/-- Domainhood needed to state the DVR structure on the completed quotient
by the mapped second-parameter ideal. -/
private theorem completionQuotientSecondRegularParameter_isDomain
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let I := Ideal.span ({y} : Set R)
    IsDomain (Rhat ⧸ I.map (algebraMap R Rhat)) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let I : Ideal R := Ideal.span ({y} : Set R)
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hgeometry.1
  have hIPrime :
      (I.map (algebraMap R Rhat)).IsPrime := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    exact Ideal.isPrime_span_singleton_of_prime hgeometry.2.2.2.2
  let : (I.map (algebraMap R Rhat)).IsPrime := hIPrime
  exact (Ideal.Quotient.isDomain_iff_prime
    (I.map (algebraMap R Rhat))).mpr inferInstance

/-- The quotient of the maximal-adic completion by the extension of the
second parameter of a regular pair is a DVR. -/
theorem completionQuotientSecondRegularParameter_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let I := Ideal.span ({y} : Set R)
    @IsDiscreteValuationRing
      (Rhat ⧸ I.map (algebraMap R Rhat)) inferInstance
      (completionQuotientSecondRegularParameter_isDomain hreg hgen) := by
  have hregSwap : IsRegular R [y, x] :=
    IsLocalRing.isRegular_of_perm hreg (List.Perm.swap x y []).symm
  have hgenSwap : Ideal.ofList [y, x] = maximalIdeal R := by
    calc
      Ideal.ofList [y, x] = Ideal.ofList [x, y] := by
        apply congrArg Ideal.span
        ext z
        simp [or_comm]
      _ = maximalIdeal R := hgen
  exact completionQuotientFirstRegularParameter_isDVR hregSwap hgenSwap

/-- The literal quotient by the completed second parameter is a domain.
This is separated out so downstream proofs can install the domain instance
before installing the DVR instance. -/
theorem completedRegularPair_secondParameterQuotient_isDomain
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let yhat := algebraMap R Rhat y
    IsDomain (Rhat ⧸ Ideal.span ({yhat} : Set Rhat)) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let yhat : Rhat := algebraMap R Rhat y
  let Iy : Ideal Rhat := Ideal.span ({yhat} : Set Rhat)
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hgeometry.1
  let : Iy.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime hgeometry.2.2.2.2
  exact (Ideal.Quotient.isDomain_iff_prime Iy).mpr inferInstance

/-- Literal second-parameter form of
`completionQuotientSecondRegularParameter_isDVR`. -/
theorem completedRegularPair_secondParameterQuotient_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let yhat := algebraMap R Rhat y
    @IsDiscreteValuationRing
      (Rhat ⧸ Ideal.span ({yhat} : Set Rhat)) inferInstance
      (completedRegularPair_secondParameterQuotient_isDomain hreg hgen) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let yhat : Rhat := algebraMap R Rhat y
  let Iy : Ideal Rhat := Ideal.span ({yhat} : Set Rhat)
  let : IsDomain (Rhat ⧸ Iy) :=
    completedRegularPair_secondParameterQuotient_isDomain hreg hgen
  have hDVR := completionQuotientSecondRegularParameter_isDVR hreg hgen
  let Imap : Ideal Rhat :=
    (Ideal.span ({y} : Set R)).map (algebraMap R Rhat)
  have hImap : Imap = Iy := by
    simp only [Imap, Iy, yhat, Ideal.map_span, Set.image_singleton]
  let eI : (Rhat ⧸ Imap) ≃+* (Rhat ⧸ Iy) := RingEquiv.cast hImap
  let : IsDomain (Rhat ⧸ Imap) :=
    eI.toMulEquiv.isDomain (Rhat ⧸ Iy)
  let : IsDiscreteValuationRing (Rhat ⧸ Imap) := by
    exact hDVR
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eI

/-- In the completed second-parameter quotient, the image of the first
parameter generates the maximal ideal. -/
theorem completedRegularPair_secondParameterQuotient_maximalIdeal_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let xhat := algebraMap R Rhat x
    let yhat := algebraMap R Rhat y
    let Iy := Ideal.span ({yhat} : Set Rhat)
    let Q := Rhat ⧸ Iy
    letI : IsDomain Q :=
      completedRegularPair_secondParameterQuotient_isDomain hreg hgen
    letI : IsDiscreteValuationRing Q :=
      completedRegularPair_secondParameterQuotient_isDVR hreg hgen
    maximalIdeal Q =
      Ideal.span ({Ideal.Quotient.mk Iy xhat} : Set Q) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let xhat : Rhat := algebraMap R Rhat x
  let yhat : Rhat := algebraMap R Rhat y
  let Iy : Ideal Rhat := Ideal.span ({yhat} : Set Rhat)
  let Q := Rhat ⧸ Iy
  let : IsDomain Q :=
    completedRegularPair_secondParameterQuotient_isDomain hreg hgen
  let : IsDiscreteValuationRing Q :=
    completedRegularPair_secondParameterQuotient_isDVR hreg hgen
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  have hmaxMap :
      (maximalIdeal Rhat).map (Ideal.Quotient.mk Iy) =
        maximalIdeal Q :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk Iy) Ideal.Quotient.mk_surjective
  have hyzero : Ideal.Quotient.mk Iy yhat = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self yhat)
  calc
    maximalIdeal Q =
        (maximalIdeal Rhat).map (Ideal.Quotient.mk Iy) := hmaxMap.symm
    _ = (Ideal.ofList [xhat, yhat]).map (Ideal.Quotient.mk Iy) := by
      rw [hgeometry.2.2.1]
    _ = Ideal.ofList
        [Ideal.Quotient.mk Iy xhat, Ideal.Quotient.mk Iy yhat] := by
      exact Ideal.map_ofList (Ideal.Quotient.mk Iy) [xhat, yhat]
    _ = Ideal.span ({Ideal.Quotient.mk Iy xhat} : Set Q) := by
      rw [hyzero]
      rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil,
        sup_bot_eq, Ideal.span_singleton_zero, sup_bot_eq]

/-- The canonical source map to the residue field of the completed
second-parameter quotient is surjective.  This is the exact mod-parameter
input used to prove surjectivity of the inner power-series evaluation. -/
theorem completedRegularPair_secondParameterQuotient_residue_surjective
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let yhat := algebraMap R Rhat y
    let Iy := Ideal.span ({yhat} : Set Rhat)
    let Q := Rhat ⧸ Iy
    letI : IsDomain Q :=
      completedRegularPair_secondParameterQuotient_isDomain hreg hgen
    letI : IsDiscreteValuationRing Q :=
      completedRegularPair_secondParameterQuotient_isDVR hreg hgen
    Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal Q)).comp
        ((Ideal.Quotient.mk Iy).comp (algebraMap R Rhat))) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let yhat : Rhat := algebraMap R Rhat y
  let Iy : Ideal Rhat := Ideal.span ({yhat} : Set Rhat)
  let Q := Rhat ⧸ Iy
  let qmap : Rhat →+* Q := Ideal.Quotient.mk Iy
  let f : R →+* Q := qmap.comp (algebraMap R Rhat)
  let : IsDomain Q :=
    completedRegularPair_secondParameterQuotient_isDomain hreg hgen
  let : IsDiscreteValuationRing Q :=
    completedRegularPair_secondParameterQuotient_isDVR hreg hgen
  let : IsLocalHom qmap :=
    IsLocalHom.of_surjective qmap Ideal.Quotient.mk_surjective
  have hquotientResidue :
      Function.Surjective
        (IsLocalRing.ResidueField.map qmap) := by
    intro z
    obtain ⟨q, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨IsLocalRing.residue Rhat a, ?_⟩
    exact IsLocalRing.ResidueField.map_residue qmap a
  have hsourceResidue :
      Function.Surjective
        (IsLocalRing.ResidueField.map f) := by
    have hcomp := hquotientResidue.comp
      (AdicCompletion.residueField_map_bijective R).2
    simpa only [f, qmap, IsLocalRing.ResidueField.map_comp,
      RingHom.coe_comp] using hcomp
  intro z
  obtain ⟨w, hw⟩ := hsourceResidue z
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective w
  refine ⟨r, ?_⟩
  change IsLocalRing.residue Q (f r) = z
  rw [← IsLocalRing.ResidueField.map_residue, hr]
  exact hw

end EtaleFundamentalGroups.Kummer

end
