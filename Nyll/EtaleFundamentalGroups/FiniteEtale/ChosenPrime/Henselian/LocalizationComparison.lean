/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.LocalFactor
import Nyll.SchemeTheory.FiniteEtale.Henselian.PointedEtale

/-!
# Recovering the input prime from the Tag 00UJ chosen factor

Over a Henselian local base, the pointed etale neighbourhood produced by
Tag 00UJ becomes the base itself after localization at its selected point.
Consequently the prime-local ring of the chosen idempotent factor is the
prime-local ring of the *input* algebra at the *input* prime.  The comparison
is constructed from the contraction equality returned by 00UJ; no separately
chosen prime or ideal equality is assumed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u v

/-- The local factor cut out by Tag 00UJ recovers the prime which was supplied
to the Tag construction.

The pointed etale localization is first identified with the Henselian base.
After this cancellation, the contraction equality `hP'q` identifies the
transported tensor-product prime with `q`; localizing gives the displayed
equivalence. -/
noncomputable def etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R]
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R C)
        (P.over_def (IsLocalRing.maximalIdeal R))))
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S)) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (q : Ideal S) [q.IsPrime]
    (hP'q :
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = q) :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime q := by
  dsimp only
  let T := C ⊗[R] S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let pointed : R ≃ₐ[R] Localization.AtPrime P :=
    henselianPointedEtaleLocalizationAlgEquiv P hres
  let Cₚ := Localization.AtPrime P
  let TS := Cₚ ⊗[R] S
  let φ : T →ₐ[C] TS :=
    Algebra.TensorProduct.map (Algebra.ofId C Cₚ) (AlgHom.id R S)
  letI : Algebra T TS := φ.toAlgebra
  letI : IsScalarTower C T TS :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  letI : IsScalarTower R T TS :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      simp [RingHom.algebraMap_toAlgebra, φ])
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid T P.primeCompl) TS := by
    exact IsLocalization.tensorProduct_tensorProduct
      R S P.primeCompl Cₚ (by
        ext s
        change φ (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        change (Algebra.TensorProduct.map
          (Algebra.ofId C Cₚ) (AlgHom.id R S))
            (1 ⊗ₜ[R] s) = 1 ⊗ₜ[R] s
        rw [Algebra.TensorProduct.map_tmul]
        simp)
  let cancel : TS ≃ₐ[R] S :=
    (Algebra.TensorProduct.congr pointed.symm (AlgEquiv.refl)).trans
      (Algebra.TensorProduct.lid R S)
  let PTS : Ideal TS := P'.map (algebraMap T TS)
  have hPdisj :
      Disjoint
        ((Algebra.algebraMapSubmonoid T P.primeCompl : Submonoid T) : Set T)
        (P' : Set T) :=
    Ideal.disjoint_primeCompl_of_liesOver P' P
  letI : PTS.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T P.primeCompl) TS P'
      inferInstance hPdisj
  have hPTSoverP' : PTS.LiesOver P' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T P.primeCompl) TS hPdisj
  have hPTSunder : PTS.comap (algebraMap T TS) = P' :=
    hPTSoverP'.over.symm
  have hcancel_right (s : S) :
      cancel (algebraMap T TS
        (Algebra.TensorProduct.includeRight s)) = s := by
    change (Algebra.TensorProduct.lid R S)
      ((Algebra.TensorProduct.congr pointed.symm (AlgEquiv.refl))
        ((Algebra.TensorProduct.map
          (Algebra.ofId C Cₚ) (AlgHom.id R S))
            (1 ⊗ₜ[R] s))) = s
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have hcancel_symm_right (s : S) :
      cancel.symm s =
        algebraMap T TS (Algebra.TensorProduct.includeRight s) :=
    (cancel.eq_symm_apply.mpr (hcancel_right s)).symm
  have hPTScancel : PTS.map (cancel.toRingEquiv : TS →+* S) = q := by
    ext s
    rw [Ideal.map_comap_of_equiv cancel.toRingEquiv]
    change cancel.symm s ∈ PTS ↔ s ∈ q
    rw [hcancel_symm_right]
    change Algebra.TensorProduct.includeRight s ∈
      PTS.comap (algebraMap T TS) ↔ s ∈ q
    rw [hPTSunder]
    change s ∈
      P'.comap Algebra.TensorProduct.includeRight.toRingHom ↔ s ∈ q
    rw [hP'q]
  have hPTScomap : PTS = q.comap cancel.toRingHom := by
    symm
    rw [← hPTScancel, Ideal.map_comap_of_equiv cancel.toRingEquiv]
    exact Ideal.comap_of_equiv cancel.toRingEquiv
  let TSp := Localization.AtPrime PTS
  let Sp := Localization.AtPrime q
  let cancelLocal : TSp ≃ₐ[R] Sp :=
    Localization.localAlgEquiv PTS q cancel hPTScomap
  letI : IsLocalization P'.primeCompl (Localization.AtPrime Q) := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (.powers e) (Localization.AtPrime Q) Q
    have hsub :
        (Q.comap (algebraMap T D)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ Q.comap (algebraMap T D)) ↔ x ∉ P'
      rw [Q.over_def P']
    exact hsub ▸ hloc
  letI : IsLocalization P'.primeCompl TSp := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid T P.primeCompl) TSp PTS
    have hsub :
        (PTS.comap (algebraMap T TS)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ PTS.comap (algebraMap T TS)) ↔ x ∉ P'
      rw [hPTSunder]
    exact hsub ▸ hloc
  let localFactor : Localization.AtPrime Q ≃ₐ[T] TSp :=
    IsLocalization.algEquiv P'.primeCompl
      (Localization.AtPrime Q) TSp
  exact localFactor.restrictScalars R |>.trans cancelLocal

/-- The input-prime comparison with the source `R`-algebra fixed to the
literal composite through the pointed localization.  This is the instance
shape used by `etaleChosenLocalFactor_henselian_boundaryAway`; the underlying
ring equivalence is the canonical comparison above. -/
noncomputable def
    etaleChosenLocalFactor_henselian_inputPrimeCompositeAlgEquiv
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R]
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Etale R C]
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R C)
        (P.over_def (IsLocalRing.maximalIdeal R))))
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S)) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (q : Ideal S) [q.IsPrime]
    (hP'q :
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = q) :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    letI : Algebra R Dₚ :=
      ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
    Dₚ ≃ₐ[R] Localization.AtPrime q := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  letI : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  letI : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let defaultRDAlgebra : Algebra R Dₚ := inferInstance
  let Edefault :
      @AlgEquiv R Dₚ (Localization.AtPrime q)
        _ _ _ defaultRDAlgebra _ :=
    etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
      (R := R) P hres e P' heP' q hP'q
  let ERing : Dₚ ≃+* Localization.AtPrime q := Edefault.toRingEquiv
  have hdefaultCommutes (r : R) :
      ERing (@algebraMap R Dₚ _ _ defaultRDAlgebra r) =
        algebraMap R (Localization.AtPrime q) r :=
    Edefault.commutes r
  let rDAlgebra : Algebra R Dₚ :=
    ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
  letI : SMul R Dₚ := defaultRDAlgebra.toSMul
  letI : Algebra R Dₚ := defaultRDAlgebra
  letI : IsScalarTower R C Cₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower C Cₚ Dₚ := inferInstance
  letI : IsScalarTower R C Dₚ := inferInstance
  have hdefaultTower (r : R) :
      @algebraMap R Dₚ _ _ defaultRDAlgebra r =
        algebraMap C Dₚ (algebraMap R C r) :=
    IsScalarTower.algebraMap_apply R C Dₚ r
  have hsource (r : R) :
      @algebraMap R Dₚ _ _ rDAlgebra r =
        @algebraMap R Dₚ _ _ defaultRDAlgebra r := by
    change algebraMap Cₚ Dₚ (algebraMap R Cₚ r) =
      @algebraMap R Dₚ _ _ defaultRDAlgebra r
    rw [hdefaultTower, IsScalarTower.algebraMap_apply R C Cₚ,
      ← IsScalarTower.algebraMap_apply C Cₚ Dₚ]
  letI : SMul R Dₚ := rDAlgebra.toSMul
  letI : Algebra R Dₚ := rDAlgebra
  refine
    { toRingEquiv := ERing
      commutes' := fun r ↦ ?_ }
  rw [hsource]
  exact hdefaultCommutes r

/-- Apply Tag 00UJ to `q` itself and return its chosen factor together with
the canonical recovery of `S_q`.  All comparison data are produced from the
Tag contraction equality. -/
theorem exists_etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    [Algebra.QuasiFiniteAt R q] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra.Etale R C)
      (P : Ideal C) (_ : P.IsPrime)
      (_ : P.LiesOver (IsLocalRing.maximalIdeal R))
      (e : C ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (C ⊗[R] S))
      (_ : P'.IsPrime) (_ : P'.LiesOver P)
      (heP' : e ∉ P'),
        P'.comap Algebra.TensorProduct.includeRight.toRingHom = q ∧
        Function.Bijective
          (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
            (Algebra.ofId R C)
            (P.over_def (IsLocalRing.maximalIdeal R))) ∧
        Module.Finite C (Localization.Away e) ∧
        (∀ P'' : Ideal (C ⊗[R] S),
          P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') ∧
        let Q := etaleChosenAwayPrime e P'
        letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
        Nonempty
          (Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime q) := by
  obtain ⟨C, _, _, _, P, _, _, e, heidem, P', _, _,
      hP'q, heP', hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
      (IsLocalRing.maximalIdeal R) q
  refine ⟨C, inferInstance, inferInstance, inferInstance,
    P, inferInstance, inferInstance, e, heidem,
    P', inferInstance, inferInstance, heP',
    hP'q, hres, hfinite, hunique, ?_⟩
  exact ⟨etaleChosenLocalFactor_henselian_inputPrimeAlgEquiv
    (R := R) P hres e P' heP' q hP'q⟩

end EtaleFundamentalGroups

end
