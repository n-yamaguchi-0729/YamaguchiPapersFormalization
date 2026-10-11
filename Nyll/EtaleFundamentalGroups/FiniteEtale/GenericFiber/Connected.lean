/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component

/-!
# Connected finite-etale algebras over normal domains

A connected finite-etale algebra over an integrally closed domain has only
one generic-fibre field component.  The selected-component normalization is
an idempotent factor of the algebra; connectedness makes that factor the
whole algebra, and hence embeds the algebra into a field.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uT uK

/-- A finite-etale algebra over an integrally closed domain whose prime
spectrum is connected is a domain. -/
theorem finiteEtale_isDomain_of_connectedSpace_primeSpectrum
    {R : Type uR} {T : Type uT} {K : Type uK}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [ConnectedSpace (PrimeSpectrum T)] : IsDomain T := by
  classical
  let G := T ⊗[R] K
  have hincludeLeft : Function.Injective
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] G) :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  let : Nontrivial T :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial G := Function.Injective.nontrivial hincludeLeft
  let M : MaximalSpectrum G :=
    Classical.choice (inferInstance : Nonempty (MaximalSpectrum G))
  let m : Ideal G := M.asIdeal
  let : m.IsMaximal := M.2
  let D := integralClosure R (FiniteEtaleGenericFiberComponent m)
  let g : T →ₐ[R] D := genericFiberComponentToIntegralClosure m
  have hg : Function.Surjective g :=
    genericFiberComponentToIntegralClosure_surjective m
  let : Algebra.Etale R D :=
    integralClosure_etale_genericFiberComponent m
  let : Algebra T D := g.toAlgebra
  let : IsScalarTower R T D :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext r
      rfl
  let : Algebra.FormallyEtale T D :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hkerIdempotent : IsIdempotentElem (RingHom.ker g.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective hg).mp inferInstance
  have hkerFG : (RingHom.ker g.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective g hg
  obtain ⟨e, he, hker⟩ :=
    ((RingHom.ker g.toRingHom).isIdempotentElem_iff_of_fg hkerFG).mp
      hkerIdempotent
  have he_zero_or_one : e = 0 ∨ e = 1 := by
    have hopen : IsClopen (PrimeSpectrum.basicOpen e) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
    rcases isClopen_iff.mp hopen with hopen | hopen
    · left
      have hbasic : PrimeSpectrum.basicOpen e =
          PrimeSpectrum.basicOpen (0 : T) := by
        apply SetLike.ext'
        rw [PrimeSpectrum.basicOpen_zero]
        simpa only [TopologicalSpace.Opens.coe_bot] using hopen
      exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem he
        (show IsIdempotentElem (0 : T) by exact zero_mul 0)
        hbasic
    · right
      have hbasic : PrimeSpectrum.basicOpen e =
          PrimeSpectrum.basicOpen (1 : T) := by
        apply SetLike.ext'
        rw [PrimeSpectrum.basicOpen_one]
        simpa only [TopologicalSpace.Opens.coe_top] using hopen
      exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem he
        (show IsIdempotentElem (1 : T) by exact one_mul 1)
        hbasic
  have he_ne_one : e ≠ 1 := by
    intro heone
    have htop : RingHom.ker g.toRingHom = ⊤ := by
      rw [hker, heone]
      simp
    have hone : (1 : T) ∈ RingHom.ker g.toRingHom := by rw [htop]; simp
    have hD : (1 : D) = 0 := by
      simpa only [RingHom.mem_ker, map_one] using hone
    exact one_ne_zero hD
  have hezero : e = 0 := he_zero_or_one.resolve_right he_ne_one
  have hkerbot : RingHom.ker g.toRingHom = ⊥ := by
    rw [hker, hezero]
    simp
  have hginjective : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot]
    exact hkerbot
  exact Function.Injective.isDomain g hginjective

/-- A finite-etale algebra over an integrally closed domain whose prime
spectrum is connected is integrally closed. -/
theorem finiteEtale_isIntegrallyClosed_of_connectedSpace_primeSpectrum
    {R : Type uR} {T : Type uT} {K : Type uK}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [ConnectedSpace (PrimeSpectrum T)] : IsIntegrallyClosed T := by
  classical
  let G := T ⊗[R] K
  have hincludeLeft : Function.Injective
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] G) :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  let : Nontrivial T :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  let : Nontrivial G := Function.Injective.nontrivial hincludeLeft
  let M : MaximalSpectrum G :=
    Classical.choice (inferInstance : Nonempty (MaximalSpectrum G))
  let m : Ideal G := M.asIdeal
  let : m.IsMaximal := M.2
  let L := FiniteEtaleGenericFiberComponent m
  let D := integralClosure R L
  let g : T →ₐ[R] D := genericFiberComponentToIntegralClosure m
  have hg : Function.Surjective g :=
    genericFiberComponentToIntegralClosure_surjective m
  let : Algebra.Etale R D :=
    integralClosure_etale_genericFiberComponent m
  let : Algebra T D := g.toAlgebra
  let : IsScalarTower R T D :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext r
      rfl
  let : Algebra.FormallyEtale T D :=
    Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hkerIdempotent : IsIdempotentElem (RingHom.ker g.toRingHom) :=
    (Algebra.FormallyEtale.iff_of_surjective hg).mp inferInstance
  have hkerFG : (RingHom.ker g.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective g hg
  obtain ⟨e, he, hker⟩ :=
    ((RingHom.ker g.toRingHom).isIdempotentElem_iff_of_fg hkerFG).mp
      hkerIdempotent
  have he_zero_or_one : e = 0 ∨ e = 1 := by
    have hopen : IsClopen (PrimeSpectrum.basicOpen e) :=
      PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
    rcases isClopen_iff.mp hopen with hopen | hopen
    · left
      have hbasic : PrimeSpectrum.basicOpen e =
          PrimeSpectrum.basicOpen (0 : T) := by
        apply SetLike.ext'
        rw [PrimeSpectrum.basicOpen_zero]
        simpa only [TopologicalSpace.Opens.coe_bot] using hopen
      exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem he
        (show IsIdempotentElem (0 : T) by exact zero_mul 0)
        hbasic
    · right
      have hbasic : PrimeSpectrum.basicOpen e =
          PrimeSpectrum.basicOpen (1 : T) := by
        apply SetLike.ext'
        rw [PrimeSpectrum.basicOpen_one]
        simpa only [TopologicalSpace.Opens.coe_top] using hopen
      exact PrimeSpectrum.basicOpen_injOn_isIdempotentElem he
        (show IsIdempotentElem (1 : T) by exact one_mul 1)
        hbasic
  have he_ne_one : e ≠ 1 := by
    intro heone
    have htop : RingHom.ker g.toRingHom = ⊤ := by
      rw [hker, heone]
      simp
    have hone : (1 : T) ∈ RingHom.ker g.toRingHom := by rw [htop]; simp
    have hD : (1 : D) = 0 := by
      simpa only [RingHom.mem_ker, map_one] using hone
    exact one_ne_zero hD
  have hezero : e = 0 := he_zero_or_one.resolve_right he_ne_one
  have hkerbot : RingHom.ker g.toRingHom = ⊥ := by
    rw [hker, hezero]
    simp
  have hginjective : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot]
    exact hkerbot
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R K G := Algebra.TensorProduct.right_isScalarTower
  let commK : (K ⊗[R] T) ≃ₐ[K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm R K T).toRingEquiv
      commutes' := by
        intro k
        exact (Algebra.TensorProduct.right_algebraMap_apply k).symm }
  let : Module.Finite K G :=
    Module.Finite.of_surjective commK.toLinearMap commK.surjective
  let : Field L := Ideal.Quotient.field m
  let : Module.Finite K L :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      Ideal.Quotient.mk_surjective
  let : IsIntegrallyClosed D :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) (L := L) K
  let eTD : T ≃+* D := RingEquiv.ofBijective g.toRingHom ⟨hginjective, hg⟩
  exact IsIntegrallyClosed.of_equiv eTD.symm

end EtaleFundamentalGroups
