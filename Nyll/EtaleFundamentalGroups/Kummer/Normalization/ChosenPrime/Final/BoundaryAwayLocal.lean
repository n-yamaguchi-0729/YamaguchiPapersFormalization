/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Away.AlgEquivTransport
import Nyll.EtaleFundamentalGroups.FiniteEtale.ChosenPrime.BoundaryAway
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.Tower.FinalNormalizationLocal

/-!
# Primitive boundary Away at one final tensor-component prime

The non-Henselian Tag construction produces the primitive boundary Away map
on its chosen prime-local factor.  If the already selected normalization
chain identifies that local factor with the transported second-stage prime,
the literal recovery of the final tensor component identifies it in turn
with the chosen prime of the original final component.  This file performs
that single local transport; it makes no global etaleness claim.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uR uC uS uK uF uF' uL

/-- The primitive Tag Away map transports to an arbitrary normalization
prime `p` of the literal final tensor component `m`.

`ETag` is the source-produced normalization-localization comparison ending
at the prime obtained by transporting `p` to the selected second-stage
component.  No equality between independently selected components or primes
is assumed. -/
theorem etaleChosenLocalFactor_finalComponent_boundaryAway_local
    {R : Type uR} {C : Type uC} {S : Type uS}
    {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
    [CommRing R] [CommRing C] [CommRing S]
    [IsNoetherianRing C]
    [Algebra R C] [Algebra R S]
    [Field K] [Field F] [Field F'] [Field L]
    [Algebra K F] [Algebra F F'] [Algebra K F']
    [IsScalarTower K F F'] [Algebra K L]
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
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
    [Algebra (Localization.AtPrime P) F']
    [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let Cₚ := Localization.AtPrime P
      let Pm := GenericTensorFieldComponent m
      letI : Algebra Cₚ Pm :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
      Ideal (integralClosure Cₚ Pm))
    [p.IsPrime]
    (ETag :
      let Q := etaleChosenAwayPrime e P'
      letI : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
      letI : Q.LiesOver P' :=
        etaleChosenAwayPrime_liesOver e P' heP'
      letI : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
      let Cₚ := Localization.AtPrime P
      let Dₚ := Localization.AtPrime Q
      letI : Algebra Cₚ Dₚ :=
        Localization.AtPrime.algebraOfLiesOver P Q
      let n := genericTensorTowerIntermediateIdeal
        (K := K) (F := F) (F' := F') (L := L) m
      letI : n.IsMaximal :=
        genericTensorTowerIntermediateIdeal_isMaximal
          (K := K) (F := F) (F' := F') (L := L) m
      let q := genericTensorTowerSecondIdeal
        (K := K) (F := F) (F' := F') (L := L) m
      letI : q.IsMaximal :=
        genericTensorTowerSecondIdeal_isMaximal
          (K := K) (F := F) (F' := F') (L := L) m
      let Pm := GenericTensorFieldComponent m
      let Pq := GenericTensorFieldComponent q
      letI : Algebra Cₚ Pm :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
      letI : Algebra Cₚ Pq :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) q
      let p' := genericTensorTowerFinalComponentIntegralClosurePrime
        (B := Cₚ) (K := K) (F := F) (F' := F') (L := L) m p
      letI : p'.IsPrime :=
        genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
          (B := Cₚ) (K := K) (F := F) (F' := F') (L := L) m p
      Dₚ ≃ₐ[Cₚ] Localization.AtPrime p') :
    let Cₚ := Localization.AtPrime P
    let Pm := GenericTensorFieldComponent m
    letI : Algebra Cₚ Pm :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
    let Dfinal := Localization.AtPrime p
    letI : Algebra Cₚ Dfinal := inferInstance
    let fCₚ : Cₚ := algebraMap C Cₚ (algebraMap R C f)
    @Algebra.Etale
      (Localization.Away fCₚ)
      (Localization.Away (algebraMap Cₚ Dfinal fCₚ))
      _ _
      (Localization.awayMap (algebraMap Cₚ Dfinal) fCₚ).toAlgebra := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' :=
    etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let q := genericTensorTowerSecondIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let Pm := GenericTensorFieldComponent m
  let Pq := GenericTensorFieldComponent q
  let : Algebra Cₚ Pm :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
  let : Algebra Cₚ Pq :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) q
  let p' := genericTensorTowerFinalComponentIntegralClosurePrime
    (B := Cₚ) (K := K) (F := F) (F' := F') (L := L) m p
  let : p'.IsPrime :=
    genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
      (B := Cₚ) (K := K) (F := F) (F' := F') (L := L) m p
  let Efinal : Localization.AtPrime p ≃ₐ[Cₚ]
      Localization.AtPrime p' :=
    genericTensorTowerFinalComponentIntegralClosureLocalizationAlgEquiv
      (B := Cₚ) (K := K) (F := F) (F' := F') (L := L) m p
  let Dfinal := Localization.AtPrime p
  let : Algebra Cₚ Dfinal := inferInstance
  let Etotal : Dₚ ≃ₐ[Cₚ] Dfinal := ETag.trans Efinal.symm
  let fCₚ : Cₚ := algebraMap C Cₚ (algebraMap R C f)
  have hTag :
      @Algebra.Etale
        (Localization.Away fCₚ)
        (Localization.Away (algebraMap Cₚ Dₚ fCₚ))
        _ _
        (Localization.awayMap (algebraMap Cₚ Dₚ) fCₚ).toAlgebra :=
    etaleChosenLocalFactor_pointed_boundaryAway
      (R := R) (C := C) (S := S)
      f hAway P e P' heP' hfinite hunique
  exact localization_awayMap_etale_of_tower_algEquiv
    (A := Cₚ) (C := Cₚ) Etotal fCₚ hTag

end EtaleFundamentalGroups.Kummer

end
