/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.KrullDimension.Zero
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.MaximalAdicCompletionGeometry
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# Prime ideals containing one member of a regular pair

In a two-dimensional regular local ring presented by a regular parameter
pair, every prime containing the first parameter is either its principal
height-one prime or the closed point.  This elementary dichotomy is useful
after maximal-adic completion: contraction to the original non-closed
branch rules out the second alternative and hence identifies the completed
branch without a formal-fibre comparison hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence

universe u

/-- Domainhood needed to state the DVR structure on the completed
parameter quotient. -/
private theorem completionQuotientFirstRegularParameter_isDomain
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let I := Ideal.span ({x} : Set R)
    IsDomain (Rhat ⧸ I.map (algebraMap R Rhat)) := by
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hIPrime :
      (I.map (algebraMap R Rhat)).IsPrime := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    exact Ideal.isPrime_span_singleton_of_prime
      (prime_first_maximalAdicCompletion_of_regularPair hreg hgen)
  let : (I.map (algebraMap R Rhat)).IsPrime := hIPrime
  exact (Ideal.Quotient.isDomain_iff_prime
    (I.map (algebraMap R Rhat))).mpr inferInstance

/-- A quotient by the first member of a regular parameter pair is a DVR
once its canonical domain structure is installed. -/
private theorem quotientFirstRegularParameter_isDVR
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    {a b : T}
    (hreg : IsRegular T [a, b])
    (hgen : Ideal.ofList [a, b] = maximalIdeal T)
    [IsDomain (T ⧸ Ideal.span ({a} : Set T))] :
    IsDiscreteValuationRing (T ⧸ Ideal.span ({a} : Set T)) := by
  let I : Ideal T := Ideal.span ({a} : Set T)
  let S := T ⧸ I
  let : I.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (prime_of_mem_regularSystem hreg hgen (by simp))
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective T S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg hgen
  have hregS : IsRegular S [Ideal.Quotient.mk I b] := by
    simpa only [I, S, List.map_cons, List.map_nil] using hquot.1
  have hgenS : Ideal.ofList [Ideal.Quotient.mk I b] = maximalIdeal S := by
    calc
      Ideal.ofList [Ideal.Quotient.mk I b] =
          (maximalIdeal T).map (Ideal.Quotient.mk I) := by
        simpa only [I, S, List.map_cons, List.map_nil] using hquot.2
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hbPrime : Prime (Ideal.Quotient.mk I b) :=
    prime_of_mem_regularSystem hregS hgenS (by simp)
  have hSNotField : ¬ IsField S := by
    intro hfield
    have hmaxBot : maximalIdeal S = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have hbMem : Ideal.Quotient.mk I b ∈ maximalIdeal S := by
      rw [← hgenS]
      exact Ideal.subset_span (by simp)
    have hbZero : Ideal.Quotient.mk I b = 0 := by
      rw [hmaxBot] at hbMem
      simpa using hbMem
    exact hbPrime.ne_zero hbZero
  have hprincipal : Submodule.IsPrincipal (maximalIdeal S) := by
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    simpa using hgenS.symm
  exact ((IsDiscreteValuationRing.TFAE S hSNotField).out 5 1).mp
    hprincipal

/-- The maximal-adic completion of a DVR is a domain, via the standard
complete valued-field model. -/
private theorem maximalAdicCompletion_of_dvr_isDomain
    {T : Type u} [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsDiscreteValuationRing T] :
    IsDomain (AdicCompletion (maximalIdeal T) T) := by
  let K := FractionRing T
  let Vhat := (standardDVFCompletionCompleteDVF T K).valuationSubring
  let : Algebra T Vhat :=
    standardDVFCompletionValuationSubringAlgebra T K
  let e : AdicCompletion (maximalIdeal T) T ≃+* Vhat :=
    (standardDVRAdicCompletionEquivCompletionValuationSubring T K).toRingEquiv
  exact e.toMulEquiv.isDomain Vhat

/-- The preceding completed domain carries the transported DVR structure. -/
private theorem maximalAdicCompletion_of_dvr_isDVR
    {T : Type u} [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsDiscreteValuationRing T] :
    @IsDiscreteValuationRing
      (AdicCompletion (maximalIdeal T) T) inferInstance
      (maximalAdicCompletion_of_dvr_isDomain (T := T)) := by
  let : IsDomain (AdicCompletion (maximalIdeal T) T) :=
    maximalAdicCompletion_of_dvr_isDomain (T := T)
  let K := FractionRing T
  let Vhat := (standardDVFCompletionCompleteDVF T K).valuationSubring
  let : Algebra T Vhat :=
    standardDVFCompletionValuationSubringAlgebra T K
  let e : Vhat ≃+* AdicCompletion (maximalIdeal T) T :=
    (standardDVRAdicCompletionEquivCompletionValuationSubring T K).symm.toRingEquiv
  exact
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

/-- The tensor/quotient comparison followed by finite base change identifies
the completed source quotient with the quotient of the completed source. -/
private noncomputable def completionQuotientRingEquiv
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (I : Ideal T) :
    AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I) ≃+*
      (AdicCompletion (maximalIdeal T) T ⧸
        I.map (algebraMap T (AdicCompletion (maximalIdeal T) T))) := by
  let S := T ⧸ I
  let That := AdicCompletion (maximalIdeal T) T
  let mT := maximalIdeal T
  letI : Module.Finite T S :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ T I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective T I)
  exact
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot That I).toRingEquiv.trans
      (tensorProductMappedIdealCompletionRingEquiv mT)).symm

/-- The completion at the image of the source maximal ideal is a domain,
because that image is the quotient's maximal ideal. -/
private theorem mappedQuotientCompletion_isDomain
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (I : Ideal T)
    (hSourceDomain : IsDomain (T ⧸ I))
    (hSourceDVR :
      @IsDiscreteValuationRing (T ⧸ I) inferInstance hSourceDomain) :
    IsDomain
      (AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I)) := by
  let S := T ⧸ I
  let mT := maximalIdeal T
  let mS := mT.map (algebraMap T S)
  let : IsDomain S := hSourceDomain
  let : IsDiscreteValuationRing S := hSourceDVR
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective T S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmS : mS = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  change IsDomain (AdicCompletion mS S)
  exact hmS.symm ▸ maximalAdicCompletion_of_dvr_isDomain (T := S)

/-- The domain above inherits the DVR structure from the maximal-adic
completion of the quotient DVR. -/
private theorem mappedQuotientCompletion_isDVR
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (I : Ideal T)
    (hSourceDomain : IsDomain (T ⧸ I))
    (hSourceDVR :
      @IsDiscreteValuationRing (T ⧸ I) inferInstance hSourceDomain)
    (hMappedDomain : IsDomain
      (AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I))) :
    @IsDiscreteValuationRing
      (AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I))
      inferInstance hMappedDomain := by
  let S := T ⧸ I
  let mT := maximalIdeal T
  let mS := mT.map (algebraMap T S)
  let : IsDomain S := hSourceDomain
  let : IsDiscreteValuationRing S := hSourceDVR
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective T S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmS : mS = maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hBundle :
      ∃ h : IsDomain (AdicCompletion mS S),
        @IsDiscreteValuationRing
          (AdicCompletion mS S) inferInstance h := by
    rw [hmS]
    exact ⟨maximalAdicCompletion_of_dvr_isDomain (T := S),
      maximalAdicCompletion_of_dvr_isDVR (T := S)⟩
  obtain ⟨_, hDVR⟩ := hBundle
  exact hDVR

/-- Completion base change carries a DVR quotient to the corresponding
quotient of the maximal-adic completion. -/
private theorem completionQuotient_isDVR_of_quotientDVR
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    (I : Ideal T)
    (hSourceDomain : IsDomain (T ⧸ I))
    (hSourceDVR :
      @IsDiscreteValuationRing (T ⧸ I) inferInstance hSourceDomain)
    (hTargetDomain : IsDomain
      (AdicCompletion (maximalIdeal T) T ⧸
        I.map (algebraMap T (AdicCompletion (maximalIdeal T) T)))) :
    @IsDiscreteValuationRing
      (AdicCompletion (maximalIdeal T) T ⧸
        I.map (algebraMap T (AdicCompletion (maximalIdeal T) T)))
      inferInstance hTargetDomain := by
  have hMappedDomain :=
    mappedQuotientCompletion_isDomain I hSourceDomain hSourceDVR
  have hMappedDVR :=
    mappedQuotientCompletion_isDVR I hSourceDomain hSourceDVR hMappedDomain
  let : IsDomain
      (AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I)) :=
    hMappedDomain
  let : IsDiscreteValuationRing
      (AdicCompletion
        ((maximalIdeal T).map (algebraMap T (T ⧸ I))) (T ⧸ I)) :=
    hMappedDVR
  let : IsDomain
      (AdicCompletion (maximalIdeal T) T ⧸
        I.map (algebraMap T (AdicCompletion (maximalIdeal T) T))) :=
    hTargetDomain
  exact
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (completionQuotientRingEquiv I)

/-- The quotient of the maximal-adic completion by the extension of the
first parameter of a regular pair is a DVR.

The source quotient has the one-element regular system given by the second
parameter, hence is a DVR.  Tensor/quotient compatibility identifies the
completed quotient with the maximal-adic completion of that DVR, and the
standard valued-field completion model supplies the target DVR structure. -/
private theorem completionQuotientFirstRegularParameter_isDVR_aux
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R)
    [IsDomain
      (AdicCompletion (maximalIdeal R) R ⧸
        (Ideal.span ({x} : Set R)).map
          (algebraMap R (AdicCompletion (maximalIdeal R) R)))] :
    IsDiscreteValuationRing
      (AdicCompletion (maximalIdeal R) R ⧸
        (Ideal.span ({x} : Set R)).map
          (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
  classical
  let I : Ideal R := Ideal.span ({x} : Set R)
  let S := R ⧸ I
  let mR := maximalIdeal R
  let : I.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (prime_of_mem_regularSystem hreg hgen (by simp))
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg hgen
  have hregS : IsRegular S [Ideal.Quotient.mk I y] := by
    simpa only [I, S, List.map_cons, List.map_nil] using hquot.1
  have hgenS : Ideal.ofList [Ideal.Quotient.mk I y] = maximalIdeal S := by
    calc
      Ideal.ofList [Ideal.Quotient.mk I y] =
          mR.map (Ideal.Quotient.mk I) := by
        simpa only [I, S, mR, List.map_cons, List.map_nil] using hquot.2
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let hSourceDomain : IsDomain S :=
    isDomain_of_regularSystem [Ideal.Quotient.mk I y] hregS hgenS
  let : IsDomain S := hSourceDomain
  let hSourceDVR : IsDiscreteValuationRing S :=
    quotientFirstRegularParameter_isDVR hreg hgen
  let : IsDiscreteValuationRing S := hSourceDVR
  exact completionQuotient_isDVR_of_quotientDVR I
    hSourceDomain hSourceDVR inferInstance

/-- The quotient of the maximal-adic completion by the extension of the
first parameter of a regular pair is a DVR. -/
theorem completionQuotientFirstRegularParameter_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let I := Ideal.span ({x} : Set R)
    @IsDiscreteValuationRing
      (Rhat ⧸ I.map (algebraMap R Rhat)) inferInstance
      (completionQuotientFirstRegularParameter_isDomain hreg hgen) := by
  dsimp only
  let : IsDomain
      (AdicCompletion (maximalIdeal R) R ⧸
        (Ideal.span ({x} : Set R)).map
          (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
    completionQuotientFirstRegularParameter_isDomain hreg hgen
  exact completionQuotientFirstRegularParameter_isDVR_aux hreg hgen

/-- A prime of the maximal-adic completion which contracts to the first
parameter prime is exactly the extension of that parameter prime.

The quotient by the mapped parameter is a DVR.  Thus a strict enlargement
would be the closed point, which is excluded by contraction to the original
non-closed branch. -/
theorem maximalAdicCompletion_prime_eq_mapped_span_first_of_under_eq
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R)
    (q : Ideal (AdicCompletion (maximalIdeal R) R)) [q.IsPrime]
    (hunder : q.under R = Ideal.span ({x} : Set R)) :
    q = Ideal.span
      ({algebraMap R (AdicCompletion (maximalIdeal R) R) x} :
        Set (AdicCompletion (maximalIdeal R) R)) := by
  classical
  let Rhat := AdicCompletion (maximalIdeal R) R
  let xhat : Rhat := algebraMap R Rhat x
  have hgeometry := maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hgeometry.1
  have hxq : Ideal.span ({xhat} : Set Rhat) ≤ q := by
    apply q.span_singleton_le_iff_mem.mpr
    change x ∈ q.under R
    rw [hunder]
    exact Ideal.mem_span_singleton_self x
  have hxNotMax : Ideal.span ({x} : Set R) ≠ maximalIdeal R := by
    let I : Ideal R := Ideal.span ({x} : Set R)
    let S := R ⧸ I
    have hxPrime : Prime x :=
      prime_of_mem_regularSystem hreg hgen (by simp)
    let : I.IsPrime :=
      Ideal.isPrime_span_singleton_of_prime hxPrime
    have hquot := regularSystem_quotientHead hreg hgen
    have hregS : IsRegular S [Ideal.Quotient.mk I y] := by
      simpa only [I, S, List.map_cons, List.map_nil] using hquot.1
    have hyRegular : IsSMulRegular S (Ideal.Quotient.mk I y) :=
      ((isRegular_cons_iff S (Ideal.Quotient.mk I y) []).mp hregS).1
    have hyNonzero : Ideal.Quotient.mk I y ≠ 0 := by
      intro hyzero
      apply (IsSMulRegular.not_zero :
        ¬ IsSMulRegular S (0 : S))
      simpa only [hyzero] using hyRegular
    intro hmax
    have hyMem : y ∈ I := by
      change y ∈ Ideal.span ({x} : Set R)
      rw [hmax]
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    exact hyNonzero (Ideal.Quotient.eq_zero_iff_mem.mpr hyMem)
  have hqNotMax : q ≠ maximalIdeal Rhat := by
    intro hqmax
    have hqUnderMax : q.under R = maximalIdeal R := by
      rw [hqmax]
      exact IsLocalRing.maximalIdeal_comap (algebraMap R Rhat)
    exact hxNotMax (hunder.symm.trans hqUnderMax)
  let Ihat : Ideal Rhat := Ideal.span ({xhat} : Set Rhat)
  let : Ihat.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime <| by
      simpa only [Rhat, xhat] using hgeometry.2.2.2.1
  let : IsDomain (Rhat ⧸ Ihat) :=
    (Ideal.Quotient.isDomain_iff_prime Ihat).mpr inferInstance
  have hmapI :
      (Ideal.span ({x} : Set R)).map (algebraMap R Rhat) = Ihat := by
    simp only [Ihat, xhat, Ideal.map_span, Set.image_singleton]
  let : IsDiscreteValuationRing (Rhat ⧸ Ihat) := by
    have hDVR := completionQuotientFirstRegularParameter_isDVR hreg hgen
    dsimp only at hDVR
    let eI :
        (Rhat ⧸ (Ideal.span ({x} : Set R)).map (algebraMap R Rhat))
          ≃+* (Rhat ⧸ Ihat) :=
      RingEquiv.cast hmapI
    let : IsDomain
        (Rhat ⧸ (Ideal.span ({x} : Set R)).map
          (algebraMap R Rhat)) :=
      eI.toMulEquiv.isDomain (Rhat ⧸ Ihat)
    let : IsDiscreteValuationRing
        (Rhat ⧸ (Ideal.span ({x} : Set R)).map
          (algebraMap R Rhat)) := by
      exact hDVR
    exact
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eI
  by_cases hqI : q = Ihat
  · simpa only [Ihat, Rhat, xhat] using hqI
  · let qbar : Ideal (Rhat ⧸ Ihat) :=
      q.map (Ideal.Quotient.mk Ihat)
    have hker : RingHom.ker (Ideal.Quotient.mk Ihat) ≤ q := by
      simpa only [Ideal.mk_ker, Ihat] using hxq
    have hqbarPrime : qbar.IsPrime :=
      Ideal.map_isPrime_of_surjective
        Ideal.Quotient.mk_surjective hker
    have hqbarNe : qbar ≠ ⊥ := by
      intro hzero
      have hqLeI : q ≤ Ihat := by
        have hqLeKer : q ≤ RingHom.ker (Ideal.Quotient.mk Ihat) :=
          (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk Ihat)).mp hzero
        simpa only [Ideal.mk_ker] using hqLeKer
      exact hqI (le_antisymm hqLeI hxq)
    have hqbarMax : qbar.IsMaximal :=
      hqbarPrime.isMaximal hqbarNe
    let : qbar.IsMaximal := hqbarMax
    have hcomapMax :
        (qbar.comap (Ideal.Quotient.mk Ihat)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective
        (Ideal.Quotient.mk Ihat) Ideal.Quotient.mk_surjective
    have hcomap : qbar.comap (Ideal.Quotient.mk Ihat) = q := by
      calc
        qbar.comap (Ideal.Quotient.mk Ihat) =
            q ⊔ RingHom.ker (Ideal.Quotient.mk Ihat) := by
          exact Ideal.comap_map_of_surjective
            (Ideal.Quotient.mk Ihat) Ideal.Quotient.mk_surjective q
        _ = q := sup_eq_left.mpr hker
    have hqMax : q.IsMaximal := by
      simpa only [hcomap] using hcomapMax
    exact (hqNotMax (IsLocalRing.eq_maximalIdeal hqMax)).elim

end EtaleFundamentalGroups.Kummer

end
