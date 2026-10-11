/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Away.EtaleExtension
import SchemeTheory.FiniteEtale.Away.AlgEquivTransport
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.HenselianBoundaryAway
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.Henselian.LocalizationComparison

/-!
# Henselian chosen-prime boundary Away without Noetherian hypotheses

The Tag 00UJ factor used in the boundary argument is an Away localization at one
idempotent.  Thus its map from the tensor product is etale outright; it need not be
treated merely as a finite formally-etale extension.  Composing boundary Away
etaleness through that etale map removes the formerly unnecessary Noetherian
hypothesis on the pointed etale base.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace EtaleFundamentalGroups

universe uR uC uS

/-- The primitive boundary Away map survives passage to the Tag idempotent
factor without a Noetherian hypothesis on the pointed base. -/
theorem etaleChosenAway_boundaryAway_without_noetherian
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [Algebra R C] [Algebra R S]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (e : C ⊗[R] S) :
    (Localization.awayMap
      (algebraMap C (Localization.Away e))
      (algebraMap R C f)).Etale := by
  let T := C ⊗[R] S
  let D := Localization.Away e
  let fC : C := algebraMap R C f
  have hTensor :
      (Localization.awayMap (algebraMap C T) fC).Etale :=
    localization_awayMap_tensorProduct_etale
      (X := S) (Y := C) f hAway
  let : Algebra.Etale T D :=
    Algebra.Etale.of_isLocalizationAway e
  exact
    localization_awayMap_etale_of_etale_extension
      (A := C) (C := T) (D := D) fC hTensor

/-- The literal boundary Away map on the chosen Tag prime-local factor,
without a Noetherian hypothesis on the pointed base.  Tag's finite-factor
and singleton-fibre outputs are still used to identify the exact prime-local
pushout. -/
theorem etaleChosenLocalFactor_pointed_boundaryAway_without_noetherian
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [Algebra R C] [Algebra R S]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (P : Ideal C) [P.IsPrime]
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' :=
      etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    @Algebra.Etale
      (Localization.Away
        (algebraMap C Cₚ (algebraMap R C f)))
      (Localization.Away
        (algebraMap Cₚ Dₚ
          (algebraMap C Cₚ (algebraMap R C f))))
      _ _
      (Localization.awayMap
        (algebraMap Cₚ Dₚ)
        (algebraMap C Cₚ (algebraMap R C f))).toAlgebra := by
  dsimp only
  let T := C ⊗[R] S
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let fC : C := algebraMap R C f
  let : Module.Finite C D := hfinite
  let : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  have hQunique : P.primesOver D = {Q} :=
    etaleChosenAway_primesOver_eq_singleton
      P e P' heP' hunique
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D P.primeCompl) Dₚ :=
    isLocalization_localizationAtPrime_of_primesOver_eq_singleton
      hQunique
  let : Algebra.IsPushout C D Cₚ Dₚ :=
    Algebra.isPushout_of_isLocalization P.primeCompl Cₚ D Dₚ
  have hD :
      (Localization.awayMap (algebraMap C D) fC).Etale :=
    etaleChosenAway_boundaryAway_without_noetherian f hAway e
  exact
    localization_awayMap_etale_of_isPushout
      (A := C) (B := D) (C := Cₚ) (D := Dₚ) fC hD

/-- Over a Henselian local base, the same source-produced Tag local factor
retains the primitive boundary Away map with no Noetherian assumption on the
pointed etale neighbourhood. -/
theorem etaleChosenLocalFactor_henselian_boundaryAway_without_noetherian
    {R : Type uR} {C : Type uC} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [HenselianLocalRing R]
    [Algebra R C] [Algebra R S] [Algebra.Etale R C]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P
        (Algebra.ofId R C) (P.over_def (maximalIdeal R))))
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    letI : Q.LiesOver P' :=
      etaleChosenAwayPrime_liesOver e P' heP'
    letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    letI : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    letI : Algebra R Dₚ :=
      ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
    @RingHom.Etale
      (Localization.Away f)
      (Localization.Away (algebraMap R Dₚ f))
      _ _
      (Localization.awayMap (algebraMap R Dₚ) f) := by
  dsimp only
  let D := Localization.Away e
  let Q : Ideal D := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' := etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let rDAlgebra : Algebra R Dₚ :=
    ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
  let : Algebra R Dₚ := rDAlgebra
  let : SMul R Dₚ := rDAlgebra.toSMul
  let : IsScalarTower R C Cₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R Cₚ Dₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let pointed : R ≃ₐ[R] Cₚ :=
    henselianPointedEtaleLocalizationAlgEquiv P hres
  let : Algebra Cₚ R := pointed.symm.toRingHom.toAlgebra
  have hCₚR : Function.Bijective (algebraMap Cₚ R) := by
    change Function.Bijective pointed.symm.toRingHom
    exact pointed.symm.bijective
  let : IsScalarTower Cₚ R Dₚ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap Cₚ Dₚ x =
      algebraMap Cₚ Dₚ
        (algebraMap R Cₚ (pointed.symm x))
    rw [show algebraMap R Cₚ (pointed.symm x) =
        pointed (pointed.symm x) by
      simpa using (pointed.commutes (pointed.symm x)).symm]
    simp
  let : Algebra.IsPushout Cₚ Dₚ R Dₚ :=
    Algebra.IsPushout.of_bijective_left R Dₚ hCₚR
  let fCₚ : Cₚ := algebraMap C Cₚ (algebraMap R C f)
  have hPointed :
      @Algebra.Etale
        (Localization.Away fCₚ)
        (Localization.Away (algebraMap Cₚ Dₚ fCₚ))
        _ _
        (Localization.awayMap
          (algebraMap Cₚ Dₚ) fCₚ).toAlgebra :=
    etaleChosenLocalFactor_pointed_boundaryAway_without_noetherian
      (R := R) (C := C) (S := S)
      f hAway P e P' heP' hfinite hunique
  have hfCₚ : algebraMap Cₚ R fCₚ = f := by
    change pointed.symm fCₚ = f
    apply pointed.injective
    rw [pointed.apply_symm_apply]
    calc
      fCₚ = algebraMap R Cₚ f :=
        (IsScalarTower.algebraMap_apply R C Cₚ f).symm
      _ = pointed f := by
        rw [← pointed.commutes f]
        simp
  have hBack :=
    localization_awayMap_etale_of_isPushout
      (A := Cₚ) (B := Dₚ) (C := R) (D := Dₚ)
      fCₚ hPointed
  rw [hfCₚ] at hBack
  exact hBack

namespace Kummer

universe uL

/-- The primitive boundary Away map at the input prime of a fixed Tag 00UJ
factor.  Every argument after `hAway` is a literal output of
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`; this declaration
keeps the chosen-factor proof independent of the existential elimination
which produces those outputs. -/
theorem etaleChosenLocalFactor_henselian_inputPrime_boundaryAway_without_noetherian
    {R C : Type uR} {S : Type uS}
    [CommRing R] [CommRing C] [CommRing S]
    [HenselianLocalRing R]
    [Algebra R C] [Algebra R S] [Algebra.Etale R C]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R S) f).Etale)
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P
        (Algebra.ofId R C) (P.over_def (maximalIdeal R))))
    (e : C ⊗[R] S)
    (P' : Ideal (C ⊗[R] S))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] S),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
    (p : Ideal S) [p.IsPrime]
    (hP'p :
      P'.comap Algebra.TensorProduct.includeRight.toRingHom = p) :
    @RingHom.Etale
      (Localization.Away f)
      (Localization.Away
        (algebraMap R (Localization.AtPrime p) f))
      _ _
      (Localization.awayMap
        (algebraMap R (Localization.AtPrime p)) f) := by
  let Q := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' :=
    etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let rDAlgebra : Algebra R Dₚ :=
    ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
  let : Algebra R Dₚ := rDAlgebra
  let : SMul R Dₚ := rDAlgebra.toSMul
  have hTag :
      @RingHom.Etale
        (Localization.Away f)
        (Localization.Away (algebraMap R Dₚ f))
        _ _
        (Localization.awayMap (algebraMap R Dₚ) f) :=
    etaleChosenLocalFactor_henselian_boundaryAway_without_noetherian
      (R := R) (C := C) (S := S)
      f hAway P hres e P' heP' hfinite hunique
  let Einput :=
    etaleChosenLocalFactor_henselian_inputPrimeCompositeAlgEquiv
      (R := R) (C := C) (S := S)
      P hres e P' heP' p hP'p
  exact localization_awayMap_etale_of_algEquiv Einput f hTag

/-- At every closed prime of a finite normalization over a Henselian local
base, the primitive boundary Away map remains etale.  The Tag neighbourhood,
idempotent factor, and exact comparison with the input prime are all produced
internally, and no Noetherian hypothesis on the Henselian base is needed. -/
theorem arbitraryNormalizationPrime_boundaryAway_local_without_noetherian
    {R : Type uR} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [Module.Finite R (integralClosure R L)]
    (f : R)
    (hAway :
      (Localization.awayMap
        (algebraMap R (integralClosure R L)) f).Etale)
    (p : Ideal (integralClosure R L)) [p.IsPrime]
    [p.LiesOver (maximalIdeal R)] :
    @RingHom.Etale
      (Localization.Away f)
      (Localization.Away
        (algebraMap R (Localization.AtPrime p) f))
      _ _
      (Localization.awayMap
        (algebraMap R (Localization.AtPrime p)) f) := by
  obtain ⟨C, _, _, _, P, _, _, e, _, P', _, _,
      hP'p, heP', hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
      (maximalIdeal R) p
  exact
    etaleChosenLocalFactor_henselian_inputPrime_boundaryAway_without_noetherian
      (R := R) (C := C) (S := integralClosure R L)
      f hAway P hres e P' heP' hfinite hunique p hP'p

end Kummer

end EtaleFundamentalGroups
