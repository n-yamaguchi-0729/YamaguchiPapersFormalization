/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RingHom.Etale
import SchemeTheory.FiniteEtale.Away.AlgEquivTransport
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.HenselianBoundaryAway
import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.RootRefinedComponentLocal
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Primitive boundary Away map on the pointed-base chosen component

The Tag prime first selects an actual generic-fibre component and a prime in
its normalization.  Refinement back along the pointed base fraction field
preserves that same prime-local factor.  Combining those source-produced
equivalences with the primitive Henselian boundary theorem transports the
literal base Away map to this pointed-base component.

The only Away hypothesis below is the original normalization hypothesis.
In particular, no Away map for a radical cover and no comparison equivalence
is assumed.

The component produced here is a quotient of
`FractionRing R ⊗[FractionRing R] L`.  It is an intermediate pointed-base
component, not yet a component of a full radical cover.  The latter requires
a further chosen-component refinement.
-/

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace EtaleFundamentalGroups

universe uR uC uL

/-- The actual pointed-base normalization factor selected by the Tag prime
retains the literal primitive boundary Away map over the Henselian base.

Both the generic component and its normalization prime are produced from
`P'`; the displayed local equivalence is returned to record that the target
is the same chosen local factor, rather than a reselected component.  This
is an intermediate component before refinement to a full radical cover. -/
theorem exists_etaleChosenLocalFactor_pointedBaseComponent_boundaryAway
    {R : Type uR} {C : Type uC} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [CommRing C] [IsDomain C] [IsNoetherianRing C]
    [Algebra R C] [Algebra.Etale R C]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    (f : R)
    (hAway :
      (Localization.awayMap
        (algebraMap R (integralClosure R L)) f).Etale)
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P
        (Algebra.ofId R C) (P.over_def (maximalIdeal R))))
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] integralClosure R L),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Q := etaleChosenAwayPrime e P'
    let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
    let : Q.LiesOver P' :=
      etaleChosenAwayPrime_liesOver e P' heP'
    let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
    let Cₚ := Localization.AtPrime P
    let Dₚ := Localization.AtPrime Q
    let : Algebra Cₚ Dₚ :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let : Algebra R Dₚ :=
      ((algebraMap Cₚ Dₚ).comp (algebraMap R Cₚ)).toAlgebra
    let K := FractionRing R
    let pointed : R ≃ₐ[R] Cₚ :=
      henselianPointedEtaleLocalizationAlgEquiv P hres
    let : Algebra Cₚ K :=
      pointedBaseReverseFractionRingAlgebra pointed
    ∃ (n : MaximalSpectrum (K ⊗[K] L)),
      letI : Algebra Cₚ (GenericTensorFieldComponent n.asIdeal) :=
        genericTensorFieldComponentLeftScalarAlgebra
          (R := Cₚ) n.asIdeal
      ∃ (p : PrimeSpectrum
          (integralClosure Cₚ
            (GenericTensorFieldComponent n.asIdeal))),
        let Dbase := Localization.AtPrime p.asIdeal
        letI : CommRing Dbase := inferInstance
        letI : Algebra Cₚ Dbase := inferInstance
        letI : Algebra R Dbase :=
          ((algebraMap Cₚ Dbase).comp
            (algebraMap R Cₚ)).toAlgebra
        Nonempty (Dₚ ≃ₐ[Cₚ] Dbase) ∧
          @Algebra.Etale
            (Localization.Away f)
            (Localization.Away (algebraMap R Dbase f))
            _ _
            (Localization.awayMap
              (algebraMap R Dbase) f).toAlgebra := by
  intro Q hQprime hQoverPrime hQoverP Cₚ Dₚ cpDpAlgebra
  obtain ⟨m, q, ⟨ETag⟩⟩ :=
    exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv
      (R := R) (C := C) (L := L)
      P e P' heP'
  intro rDpAlgebra K pointed cpKAlgebra
  have hDp :=
    etaleChosenLocalFactor_henselian_boundaryAway
      (R := R) (C := C) (S := integralClosure R L)
      f hAway P hres e P' heP' hfinite hunique
  let : IsScalarTower C Cₚ Dₚ :=
    Localization.AtPrime.instIsScalarTower P Q
  let : SMul R Dₚ := rDpAlgebra.toSMul
  let : IsScalarTower R C Cₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower R Cₚ Dₚ
      (inferInstance : SMul R Cₚ) cpDpAlgebra.toSMul rDpAlgebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : SMul Cₚ (FractionRing R) := cpKAlgebra.toSMul
  let : Module.Finite R Cₚ :=
    Module.Finite.of_surjective pointed.toLinearMap pointed.surjective
  let : FaithfulSMul R Cₚ :=
    (faithfulSMul_iff_algebraMap_injective R Cₚ).mpr <| by
      intro x y hxy
      apply pointed.injective
      calc
        pointed x = algebraMap R Cₚ x := by
          rw [← pointed.commutes x]
          simp only [Algebra.algebraMap_self_apply]
        _ = algebraMap R Cₚ y := hxy
        _ = pointed y := by
          rw [← pointed.commutes y]
          simp only [Algebra.algebraMap_self_apply]
  have hRefinement :=
    Kummer.exists_pointedRootRefinedComponent_localizationAlgEquiv
      (R := R) (C := Cₚ) (L := L)
      pointed m.asIdeal q.asIdeal
  let n : MaximalSpectrum (K ⊗[K] L) := Classical.choose hRefinement
  have hn := Classical.choose_spec hRefinement
  let : Algebra Cₚ (GenericTensorFieldComponent n.asIdeal) :=
    genericTensorFieldComponentLeftScalarAlgebra
      (R := Cₚ) (K := K) (F := K) (L := L) n.asIdeal
  obtain ⟨p, ⟨Ebase⟩⟩ := hn
  let Dbase := Localization.AtPrime p.asIdeal
  let rBaseAlgebra : Algebra R Dbase :=
    ((algebraMap Cₚ Dbase).comp (algebraMap R Cₚ)).toAlgebra
  let : Algebra R Dbase := rBaseAlgebra
  let : SMul R Dbase := rBaseAlgebra.toSMul
  let : IsScalarTower R Cₚ Dbase :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Etotal : Dₚ ≃ₐ[Cₚ] Dbase := ETag.trans Ebase
  have hBase :
      @Algebra.Etale
        (Localization.Away f)
        (Localization.Away (algebraMap R Dbase f))
        _ _
        (Localization.awayMap (algebraMap R Dbase) f).toAlgebra :=
    localization_awayMap_etale_of_tower_algEquiv Etotal f hDp
  exact ⟨n, p, ⟨Etotal⟩, hBase⟩

end EtaleFundamentalGroups

end
