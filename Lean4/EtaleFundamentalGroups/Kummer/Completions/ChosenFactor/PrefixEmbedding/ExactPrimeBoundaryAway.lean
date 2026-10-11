/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericTensor.NormalizationPrime
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.PrefixEmbeddingCompositumAway

/-!
# Exact normalization prime in the literal prefix compositum

A concrete prefix embedding into a common target field determines a literal
`Frac(C) ⊗[Frac(A)] M` component.  The boundary-Away comparison for that
component and finite-etale base change of the original normalization prime
then produce, in the same component, a prime with the original exact
ramification index.

This is the source-producing boundary between the literal-compositum
construction and complete chosen-factor terminals.  The component and prime
are constructed here; neither is supplied by the caller.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- A prefix embedding and an exact normalization prime over a regular pair
produce an exact prime, together with the boundary-Away property, in the
literal finite-etale-base-change compositum selected inside the same target
field. -/
theorem
    completeRegularPair_prefixEmbedding_actualCompositum_exactPrime_boundaryAway
    {A C F KC M P : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Module.Finite A C] [Algebra.Etale A C] [FaithfulSMul A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field M] [Algebra A M] [Algebra F M]
    [IsScalarTower A F M] [FiniteDimensional F M]
    [Algebra.IsSeparable F M]
    [Field P] [Algebra A P] [Algebra C P]
    [IsScalarTower A C P]
    [Algebra F P] [IsScalarTower A F P]
    [Algebra KC P] [IsScalarTower C KC P]
    [Module.Finite A (integralClosure A M)]
    (y z : A)
    (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (N : ℕ)
    (fPrefix : M →ₐ[F] P)
    (q : Ideal (integralClosure A M))
    (hqPrime : q.IsPrime)
    (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
    (hqExact : q.ramificationIdx A = N)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A M)) y).Etale) :
    ∃ (mKC : Ideal (KC ⊗[F] M)) (hmKC : mKC.IsMaximal),
      letI : mKC.IsMaximal := hmKC
      let Omega := GenericTensorFieldComponent mKC
      let cOmegaAlgebra : Algebra C Omega :=
        ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
      letI : Algebra C Omega := cOmegaAlgebra
      ∃ omegaToP : Omega →ₐ[KC] P,
        letI : Algebra Omega P := omegaToP.toRingHom.toAlgebra
        @IsScalarTower C KC Omega
            (inferInstance : Algebra C KC).toSMul
            (inferInstance : Algebra KC Omega).toSMul
            cOmegaAlgebra.toSMul ∧
          IsScalarTower KC Omega P ∧
            (Localization.awayMap
              (algebraMap C (integralClosure C Omega))
              (algebraMap A C y)).Etale ∧
            ∃ Q : Ideal (integralClosure C Omega),
              Q.IsPrime ∧
                Q.LiesOver
                  (Ideal.span ({algebraMap A C y} : Set C)) ∧
                Q.ramificationIdx C = N := by
  classical
  let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsDomain C := hgeometryC.2.1
  let yC := algebraMap A C y
  have hyC : Prime yC := by
    apply hgeometryC.2.2.2.2.2.1 yC
    exact List.mem_map.mpr ⟨y, by simp, rfl⟩
  have hpC : (Ideal.span ({yC} : Set C)).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hyC
  let : q.IsPrime := hqPrime
  let : q.LiesOver (Ideal.span ({y} : Set A)) := hqOver
  let : IsScalarTower F KC P :=
    regularPair_fractionFieldTower_of_finiteEtale_commonTarget
      (A := A) (C := C) (F := F) (KC := KC) (P := P)
      y z hreg hgen
  let fKC : KC →ₐ[F] P := IsScalarTower.toAlgHom F KC P
  let Eimage : IntermediateField F P := fPrefix.fieldRange
  let Kimage : IntermediateField F P := fKC.fieldRange
  let : FiniteDimensional F Eimage :=
    fPrefix.toLinearMap.finiteDimensional_range
  let eGeneric :=
    (Algebra.TensorProduct.lid F M).trans fPrefix.equivFieldRange
  let mActual := actualCompositumGenericComponentIdeal
    (A := F) (T := M) (F := F) (Omega := P)
    Eimage Kimage eGeneric
  let : mActual.IsMaximal :=
    actualCompositumGenericComponentIdeal_isMaximal
      Eimage Kimage eGeneric
  let eKC := fKC.equivFieldRange
  let eTensorKC :=
    Algebra.TensorProduct.congr eKC (AlgEquiv.refl : M ≃ₐ[F] M)
  let mKC := mActual.comap eTensorKC.toRingEquiv.toRingHom
  let : mKC.IsMaximal :=
    (inferInstance : mActual.IsMaximal).comap_bijective
      eTensorKC.toRingEquiv.toRingHom eTensorKC.bijective
  let Omega := GenericTensorFieldComponent mKC
  let cOmegaAlgebra : Algebra C Omega :=
    ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
  have hCOmegaAlgebra :
      genericTensorFieldComponentLeftScalarAlgebra (R := C) mKC =
        cOmegaAlgebra := by
    rfl
  let : Algebra C Omega := cOmegaAlgebra
  obtain ⟨omegaToP, _, _, _, _, hBoundaryTail⟩ :=
    completeRegularPair_prefixEmbedding_actualCompositum_boundaryAway
      (A := A) (C := C) (F := F) (KC := KC)
      (M := M) (P := P) y z hreg hgen hdim fPrefix hAway
  rw [hCOmegaAlgebra] at hBoundaryTail
  let : Algebra Omega P := omegaToP.toRingHom.toAlgebra
  have hBoundaryTail' :
      IsScalarTower KC Omega P ∧
        (Localization.awayMap
          (algebraMap C (integralClosure C Omega)) yC).Etale := by
    simpa only [Omega, mKC, mActual, eTensorKC, eKC,
      eGeneric, Eimage, Kimage, fKC] using hBoundaryTail
  have hTowerOmega : IsScalarTower KC Omega P := hBoundaryTail'.1
  let : IsScalarTower KC Omega P := hTowerOmega
  have hAwayOmega := hBoundaryTail'.2
  have hPrimeData :=
    exists_integralClosure_genericTensorFieldComponent_prime_liesOver_span_ramificationIdx_eq
      (A := A) (C := C) (F := F) (KC := KC) (M := M)
      y mKC q hpC
  rw [hCOmegaAlgebra] at hPrimeData
  obtain ⟨Q, hQPrime, hQOver, hQRamification⟩ := hPrimeData
  have hTowerCKCOmega : @IsScalarTower C KC Omega
      (inferInstance : Algebra C KC).toSMul
      (inferInstance : Algebra KC Omega).toSMul
      cOmegaAlgebra.toSMul := by
    refine @IsScalarTower.of_algebraMap_eq C KC Omega
      _ _ _ (inferInstance : Algebra C KC)
        (inferInstance : Algebra KC Omega) cOmegaAlgebra ?_
    intro x
    rfl
  refine ⟨mKC, inferInstance, omegaToP, hTowerCKCOmega,
    hTowerOmega, hAwayOmega, Q, hQPrime, hQOver, ?_⟩
  exact hQRamification.trans hqExact

end EtaleFundamentalGroups.Kummer

end
