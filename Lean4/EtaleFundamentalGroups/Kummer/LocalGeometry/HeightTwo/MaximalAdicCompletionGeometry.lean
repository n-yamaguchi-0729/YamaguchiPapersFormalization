/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import EtaleFundamentalGroups.Completions.Adic.MappedIdeal
import EtaleFundamentalGroups.Completions.StandardDVF.CompletionAdic
import SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# Height-two regular geometry after maximal-adic completion

Mathlib does not currently expose a general theorem saying that the
maximal-adic completion of a regular local ring is again a regular local
ring.  The height-two argument needs less.

For a regular pair, quotienting by either parameter gives a DVR.  Completion
base change identifies the quotient by the extended parameter with the
completion of that DVR, hence the extended parameter remains prime.  Flatness
preserves the regular pair, and adic separatedness together with one prime
regular parameter then proves that the completed ring is a domain.

Thus all geometry used below is produced from existing completion, tensor,
regular-sequence, and standard-DVR APIs; no analytic-irreducibility or
completion-regularity assumption is introduced.
-/

noncomputable section

open scoped BigOperators

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence

universe u

/-- A prime regular element in a local ring separated for its maximal-ideal
adic topology forces the ring to be a domain.

This is the separated analogue of `isDomain_of_prime_isSMulRegular`: the
only use of Noetherianity in that theorem is Krull intersection, which is
supplied here directly by `IsHausdorff`. -/
theorem isDomain_of_prime_isSMulRegular_of_isHausdorff_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsHausdorff (maximalIdeal R) R]
    {p : R} (hp : Prime p) (hpreg : IsSMulRegular R p) : IsDomain R := by
  have hnotPow (a : R) (ha : a ≠ 0) :
      ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
    by_contra hall
    push Not at hall
    apply ha
    exact IsHausdorff.haus (I := maximalIdeal R) inferInstance a fun n ↦ by
      exact SModEq.zero.2 <| by
        simpa [Ideal.smul_top_eq_map] using hall n
  have hbot : (⊥ : Ideal R).IsPrime := by
    rw [Ideal.isPrime_iff]
    refine ⟨bot_ne_top, ?_⟩
    intro a b hab
    simp only [Ideal.mem_bot] at hab ⊢
    by_contra hzero
    push Not at hzero
    obtain ⟨k, hak⟩ := hnotPow a hzero.1
    obtain ⟨l, hbl⟩ := hnotPow b hzero.2
    have hpMem : p ∈ maximalIdeal R := by
      rw [mem_maximalIdeal]
      exact hp.not_isUnit
    have hpow : ∀ k l : ℕ, ∀ a b : R, a * b = 0 →
        p ^ k ∣ a ∨ p ^ l ∣ b := by
      intro k
      induction k with
      | zero =>
          intro l a b hab
          exact Or.inl (by simp)
      | succ k ihK =>
          intro l
          induction l with
          | zero =>
              intro a b hab
              exact Or.inr (by simp)
          | succ l ihL =>
              intro a b hab
              have hpProd : p ∣ a * b := by rw [hab]; exact dvd_zero p
              rcases hp.dvd_mul.mp hpProd with hpa | hpb
              · obtain ⟨a', rfl⟩ := hpa
                have hab' : a' * b = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_assoc] using hab
                rcases ihK (l + 1) a' b hab' with ha' | hb'
                · left
                  obtain ⟨c, hc⟩ := ha'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
                · exact Or.inr hb'
              · obtain ⟨b', rfl⟩ := hpb
                have hab' : a * b' = 0 := by
                  apply hpreg.right_eq_zero_of_smul
                  simpa only [smul_eq_mul, mul_comm, mul_left_comm,
                    mul_assoc] using hab
                rcases ihL a b' hab' with ha' | hb'
                · exact Or.inl ha'
                · right
                  obtain ⟨c, hc⟩ := hb'
                  refine ⟨c, ?_⟩
                  rw [hc, pow_succ]
                  ac_rfl
    rcases hpow k l a b hab with ha | hb
    · apply hak
      obtain ⟨c, rfl⟩ := ha
      exact (maximalIdeal R ^ k).mul_mem_right c
        (Ideal.pow_mem_pow hpMem k)
    · apply hbl
      obtain ⟨c, rfl⟩ := hb
      exact (maximalIdeal R ^ l).mul_mem_right c
        (Ideal.pow_mem_pow hpMem l)
  let : (⊥ : Ideal R).IsPrime := hbot
  exact IsDomain.of_bot_isPrime R

/-- If a prime quotient of a Noetherian local ring is a DVR, extension of
that prime to the maximal-adic completion remains prime.

The completed quotient is first written as a tensor product, then as the
completion of the quotient DVR at its maximal ideal.  The latter is a domain
because it is canonically the valuation subring in the standard valued-field
completion. -/
theorem maximalAdicCompletion_mappedIdeal_isPrime_of_quotientDVR
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (I : Ideal B) [I.IsPrime]
    [IsDiscreteValuationRing (B ⧸ I)] :
    (I.map (algebraMap B
      (AdicCompletion (maximalIdeal B) B))).IsPrime := by
  let Bhat := AdicCompletion (maximalIdeal B) B
  let S := B ⧸ I
  let mB := maximalIdeal B
  let mS := mB.map (algebraMap B S)
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective B S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : Module.Finite B S :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ B I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective B I)
  have hmS : mS = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let K := FractionRing S
  have hDVRCompletion :
      IsDomain (AdicCompletion (maximalIdeal S) S) := by
    let Vhat := (standardDVFCompletionCompleteDVF S K).valuationSubring
    let : Algebra S Vhat :=
      standardDVFCompletionValuationSubringAlgebra S K
    let e : AdicCompletion (maximalIdeal S) S ≃+* Vhat :=
      (standardDVRAdicCompletionEquivCompletionValuationSubring S K).toRingEquiv
    exact e.toMulEquiv.isDomain
      (standardDVFCompletionCompleteDVF S K).valuationSubring
  have hMappedCompletion :
      IsDomain (AdicCompletion mS S) := by
    rw [hmS]
    exact hDVRCompletion
  let : Algebra Bhat (AdicCompletion mS S) :=
    mappedIdealCompletionAlgebraOverCompletedBase mB
  let : IsScalarTower B Bhat (AdicCompletion mS S) :=
    mappedIdealCompletionIsScalarTower mB
  let eQuotient :
      (Bhat ⧸ I.map (algebraMap B Bhat)) ≃+*
        AdicCompletion mS S :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Bhat I).toRingEquiv.trans
      (tensorProductMappedIdealCompletionAlgEquiv mB).toRingEquiv
  let : IsDomain (AdicCompletion mS S) := hMappedCompletion
  let : IsDomain (Bhat ⧸ I.map (algebraMap B Bhat)) :=
    eQuotient.toMulEquiv.isDomain (AdicCompletion mS S)
  exact (Ideal.Quotient.isDomain_iff_prime
    (I.map (algebraMap B Bhat))).mp inferInstance

/-- The first member of a regular pair remains prime after maximal-adic
completion.  Its source quotient is shown internally to be a DVR from the
one-element quotient regular system. -/
theorem prime_first_maximalAdicCompletion_of_regularPair
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {x y : B}
    (hreg : IsRegular B [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal B) :
    Prime (algebraMap B (AdicCompletion (maximalIdeal B) B) x) := by
  let I : Ideal B := Ideal.span {x}
  let S := B ⧸ I
  let Bhat := AdicCompletion (maximalIdeal B) B
  have hxPrime : Prime x :=
    prime_of_mem_regularSystem hreg hgen (by simp)
  let : I.IsPrime := by
    exact Ideal.isPrime_span_singleton_of_prime hxPrime
  let : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing S :=
    isNoetherianRing_of_surjective B S (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg hgen
  have hregS : IsRegular S [Ideal.Quotient.mk I y] := by
    simpa only [I, S, List.map_cons, List.map_nil] using hquot.1
  have hgenS : Ideal.ofList [Ideal.Quotient.mk I y] = maximalIdeal S := by
    calc
      Ideal.ofList [Ideal.Quotient.mk I y] =
          (maximalIdeal B).map (Ideal.Quotient.mk I) := by
        simpa only [I, S, List.map_cons, List.map_nil] using hquot.2
      _ = maximalIdeal S :=
        IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hdomainS : IsDomain S :=
    isDomain_of_regularSystem [Ideal.Quotient.mk I y] hregS hgenS
  let : IsDomain S := hdomainS
  have hyPrime : Prime (Ideal.Quotient.mk I y) :=
    prime_of_mem_regularSystem hregS hgenS (by simp)
  have hSNotField : ¬ IsField S := by
    intro hfield
    have hmaxBot : maximalIdeal S = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have hyMem : Ideal.Quotient.mk I y ∈ maximalIdeal S := by
      rw [← hgenS]
      exact Ideal.subset_span (by simp)
    have hyZero : Ideal.Quotient.mk I y = 0 := by
      rw [hmaxBot] at hyMem
      simpa using hyMem
    exact hyPrime.ne_zero hyZero
  have hprincipal : Submodule.IsPrincipal (maximalIdeal S) := by
    refine ⟨Ideal.Quotient.mk I y, ?_⟩
    simpa using hgenS.symm
  let : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hSNotField).out 5 1).mp hprincipal
  have hmapPrime :
      (I.map (algebraMap B Bhat)).IsPrime :=
    maximalAdicCompletion_mappedIdeal_isPrime_of_quotientDVR I
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hxHatNe : algebraMap B Bhat x ≠ 0 :=
    (FaithfulSMul.algebraMap_injective B Bhat).ne hxPrime.ne_zero
  apply (Ideal.span_singleton_prime hxHatNe).mp
  simpa [I, Ideal.map_span] using hmapPrime

/-- A regular pair stays regular and continues to generate the closed point
after maximal-adic completion.  Both parameters remain prime, and the
completed ring is a domain. -/
theorem maximalAdicCompletion_regularPair_geometry
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {x y : B}
    (hreg : IsRegular B [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal B) :
    let Bhat := AdicCompletion (maximalIdeal B) B
    IsDomain Bhat ∧
      IsRegular Bhat [algebraMap B Bhat x, algebraMap B Bhat y] ∧
      Ideal.ofList [algebraMap B Bhat x, algebraMap B Bhat y] =
        maximalIdeal Bhat ∧
      Prime (algebraMap B Bhat x) ∧
      Prime (algebraMap B Bhat y) := by
  dsimp only
  let Bhat := AdicCompletion (maximalIdeal B) B
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hregHat :
      IsRegular Bhat [algebraMap B Bhat x, algebraMap B Bhat y] := by
    simpa only [List.map_cons, List.map_nil] using
      hreg.of_faithfullyFlat (S := Bhat)
  have hgenHat :
      Ideal.ofList [algebraMap B Bhat x, algebraMap B Bhat y] =
        maximalIdeal Bhat := by
    calc
      Ideal.ofList [algebraMap B Bhat x, algebraMap B Bhat y] =
          (Ideal.ofList [x, y]).map (algebraMap B Bhat) := by
        simpa only [List.map_cons, List.map_nil] using
          (Ideal.map_ofList (algebraMap B Bhat) [x, y]).symm
      _ = (maximalIdeal B).map (algebraMap B Bhat) := by rw [hgen]
      _ = maximalIdeal Bhat :=
        (AdicCompletion.maximalIdeal_eq_map (R := B)).symm
  have hxPrime : Prime (algebraMap B Bhat x) :=
    prime_first_maximalAdicCompletion_of_regularPair hreg hgen
  have hregSwap : IsRegular B [y, x] := by
    exact IsLocalRing.isRegular_of_perm hreg
      (List.Perm.swap x y []).symm
  have hgenSwap : Ideal.ofList [y, x] = maximalIdeal B := by
    calc
      Ideal.ofList [y, x] = Ideal.ofList [x, y] := by
        apply congrArg Ideal.span
        ext z
        simp [or_comm]
      _ = maximalIdeal B := hgen
  have hyPrime : Prime (algebraMap B Bhat y) :=
    prime_first_maximalAdicCompletion_of_regularPair hregSwap hgenSwap
  have hxRegular : IsSMulRegular Bhat (algebraMap B Bhat x) :=
    ((isRegular_cons_iff Bhat (algebraMap B Bhat x)
      [algebraMap B Bhat y]).mp hregHat).1
  have hdomain : IsDomain Bhat :=
    isDomain_of_prime_isSMulRegular_of_isHausdorff_maximalIdeal
      hxPrime hxRegular
  exact ⟨hdomain, hregHat, hgenHat, hxPrime, hyPrime⟩

/-- Characteristic zero of a divisor quotient is preserved after extending
the divisor to the maximal-adic completion. -/
theorem charZero_quotient_mappedIdeal_maximalAdicCompletion
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (I : Ideal B) (hCharZero : CharZero (B ⧸ I)) :
    CharZero
      (AdicCompletion (maximalIdeal B) B ⧸
        I.map (algebraMap B
          (AdicCompletion (maximalIdeal B) B))) := by
  let Bhat := AdicCompletion (maximalIdeal B) B
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal Bhat := I.map (algebraMap B Bhat)
  have hunder : J.comap (algebraMap B Bhat) = I :=
    Ideal.comap_map_eq_self_of_faithfullyFlat
      (A := B) (B := Bhat) I
  let : CharZero (B ⧸ J.comap (algebraMap B Bhat)) := by
    rw [hunder]
    exact hCharZero
  have htarget : CharZero (Bhat ⧸ J) :=
    charZero_of_injective_algebraMap
      (Ideal.algebraMap_quotient_injective
        (R := B) (A := Bhat) (I := J))
  simpa only [J] using htarget

/-- Association with a finite product is preserved by the canonical map to
the maximal-adic completion. -/
theorem associated_fintypeProduct_maximalAdicCompletion
    {B : Type u} [CommRing B] [IsLocalRing B]
    {ι : Type*} [Fintype ι]
    (f : B) (s : ι → B)
    (hAssoc : Associated f (∏ i, s i)) :
    Associated
      (algebraMap B (AdicCompletion (maximalIdeal B) B) f)
      (∏ i, algebraMap B (AdicCompletion (maximalIdeal B) B) (s i)) := by
  simpa only [map_prod] using
    hAssoc.map (algebraMap B (AdicCompletion (maximalIdeal B) B))

end EtaleFundamentalGroups.Kummer

end
