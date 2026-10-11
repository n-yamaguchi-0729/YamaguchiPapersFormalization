/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.FractionFieldTensorComponent
import EtaleFundamentalGroups.Kummer.GenericTensor.Refinement.NormalizationLocal

/-!
# The chosen Tag prime in a root-refined generic component

A pointed etale localization over a Henselian base is the base itself.  On
fraction fields this gives inverse scalar actions.  Consequently the actual
generic component produced from the Tag prime can be refined back along the
base fraction field without choosing a new component or a new normalization
prime.

The final endpoint combines the literal fraction-field tensor coordinate
with `genericTensorRefineChosenComponentIntegralClosureLocalizationAlgEquiv`.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uC uL

/-- A pointed equivalence induces the canonical equivalence of the two
literal fraction rings. -/
noncomputable def pointedFractionRingAlgEquiv
    {R : Type uR} {C : Type uC}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C]
    (pointed : R ≃ₐ[R] C) :
    FractionRing R ≃ₐ[R] FractionRing C :=
  IsFractionRing.algEquivOfAlgEquiv pointed

/-- The reverse fraction-field action furnished by a pointed equivalence. -/
@[reducible]
noncomputable def pointedFractionRingReverseAlgebra
    {R : Type uR} {C : Type uC}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C]
    (pointed : R ≃ₐ[R] C) :
    Algebra (FractionRing C) (FractionRing R) :=
  (pointedFractionRingAlgEquiv pointed).symm.toRingHom.toAlgebra

/-- The induced `C`-action on `FractionRing R`, factored through the reverse
fraction-field action. -/
@[reducible]
noncomputable def pointedBaseReverseFractionRingAlgebra
    {R : Type uR} {C : Type uC}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C] [Algebra R C]
    (pointed : R ≃ₐ[R] C) :
    Algebra C (FractionRing R) := by
  letI : Algebra (FractionRing C) (FractionRing R) :=
    pointedFractionRingReverseAlgebra pointed
  exact ((algebraMap (FractionRing C) (FractionRing R)).comp
    (algebraMap C (FractionRing C))).toAlgebra

section FieldEquivTensorCollapse

universe uE uK uM

variable {E : Type uE} {K : Type uK} {M : Type uM}
variable [Field E] [Field K] [Field M]
variable [Algebra E K] [Algebra E M]

/-- Tensoring along a field equivalence and then multiplying gives back the
same field. -/
noncomputable def tensorAlongFieldEquivCollapseAlgEquiv
    (e : K ≃ₐ[E] E) : (K ⊗[E] M) ≃ₐ[E] M :=
  (Algebra.TensorProduct.congr e (AlgEquiv.refl : M ≃ₐ[E] M)).trans
    (Algebra.TensorProduct.lid E M)

/-- The literal component selected by the preceding collapse map. -/
noncomputable def tensorAlongFieldEquivCollapseIdeal
    (e : K ≃ₐ[E] E) : Ideal (K ⊗[E] M) :=
  RingHom.ker (tensorAlongFieldEquivCollapseAlgEquiv e).toRingHom

theorem tensorAlongFieldEquivCollapseIdeal_isMaximal
    (e : K ≃ₐ[E] E) :
    (tensorAlongFieldEquivCollapseIdeal
      (E := E) (K := K) (M := M) e).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (tensorAlongFieldEquivCollapseAlgEquiv
      (E := E) (K := K) (M := M) e).toRingHom
    (tensorAlongFieldEquivCollapseAlgEquiv
      (E := E) (K := K) (M := M) e).surjective

/-- The quotient at the literal collapse component is the original field. -/
noncomputable def tensorAlongFieldEquivCollapseComponentAlgEquiv
    (e : K ≃ₐ[E] E) :
    ((K ⊗[E] M) ⧸ tensorAlongFieldEquivCollapseIdeal
      (E := E) (K := K) (M := M) e) ≃ₐ[E] M := by
  exact Ideal.quotientKerAlgEquivOfSurjective
    (f := (tensorAlongFieldEquivCollapseAlgEquiv
      (E := E) (K := K) (M := M) e).toAlgHom)
    (tensorAlongFieldEquivCollapseAlgEquiv
      (E := E) (K := K) (M := M) e).surjective

end FieldEquivTensorCollapse

namespace Kummer

/-- A normalization prime of an actual finite generic-fibre component,
refined back along a pointed fraction-field equivalence.

The output component is a literal maximal quotient of
`FractionRing R ⊗[FractionRing R] L`.  Both its normalization prime and
the displayed local equivalence are transported from the input prime. -/
theorem exists_pointedRootRefinedComponent_localizationAlgEquiv
    {R : Type uR} {C : Type uC} {L : Type uL}
    [CommRing R] [IsDomain R]
    [CommRing C] [IsDomain C]
    [Algebra R C] [FaithfulSMul R C] [Module.Finite R C]
    [Field L] [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    (pointed : R ≃ₐ[R] C)
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal]
    (q : Ideal (integralClosure C
      (FiniteEtaleGenericFiberComponent m))) [q.IsPrime] :
    let K := FractionRing R
    letI : Algebra C K := pointedBaseReverseFractionRingAlgebra pointed
    ∃ (n : MaximalSpectrum (K ⊗[K] L)),
      letI : Algebra C (GenericTensorFieldComponent n.asIdeal) :=
        genericTensorFieldComponentLeftScalarAlgebra
          (R := C) n.asIdeal
      ∃ (p : PrimeSpectrum
          (integralClosure C
            (GenericTensorFieldComponent n.asIdeal))),
        Nonempty
          (Localization.AtPrime q ≃ₐ[C]
            Localization.AtPrime p.asIdeal) := by
  dsimp only
  let K := FractionRing R
  let E := FractionRing C
  let eFrac : K ≃ₐ[R] E := pointedFractionRingAlgEquiv pointed
  let : Algebra K E := finiteBaseFractionRingAlgebra
    (R := R) (C := C)
  let : IsScalarTower R K E :=
    FractionRing.isScalarTower_liftAlgebra R E
  let reverse : Algebra E K :=
    pointedFractionRingReverseAlgebra pointed
  let : Algebra E K := reverse
  let : SMul E K := reverse.toSMul
  let cToK : Algebra C K :=
    pointedBaseReverseFractionRingAlgebra pointed
  let : Algebra C K := cToK
  let : SMul C K := cToK.toSMul
  have hKE : algebraMap K E = eFrac.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext x
    calc
      algebraMap K E (algebraMap R K x) = algebraMap R E x :=
        (IsScalarTower.algebraMap_apply R K E x).symm
      _ = algebraMap C E (algebraMap R C x) := by
        rw [IsScalarTower.algebraMap_apply R C E]
      _ = algebraMap C E (pointed x) := by
        congr 1
        simpa only [Algebra.algebraMap_self_apply] using
          (pointed.commutes x).symm
      _ = eFrac (algebraMap R K x) := by
        symm
        exact IsFractionRing.algEquivOfAlgEquiv_algebraMap pointed x
  let : IsScalarTower K E K := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change x = eFrac.symm (algebraMap K E x)
    rw [hKE]
    exact (eFrac.symm_apply_apply x).symm
  let m₀ := finiteBaseFractionFieldTensorIdeal
    (R := R) (C := C) (L := L) m
  let : m₀.IsMaximal :=
    finiteBaseFractionFieldTensorIdeal_isMaximal
      (R := R) (C := C) (L := L) m
  let M := GenericTensorFieldComponent m₀
  let : Algebra C M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) m₀
  let q₀ := finiteBaseFractionFieldTensorIntegralClosurePrime
    (R := R) (C := C) (L := L) m q
  let : q₀.IsPrime :=
    finiteBaseFractionFieldTensorIntegralClosurePrime_isPrime
      (R := R) (C := C) (L := L) m q
  let Efield : Localization.AtPrime q ≃ₐ[C]
      Localization.AtPrime q₀ :=
    finiteBaseFractionFieldTensorIntegralClosureLocalizationAlgEquiv
      (R := R) (C := C) (L := L) m q
  let eBase : K ≃ₐ[E] E :=
    { toRingEquiv := eFrac.toRingEquiv
      commutes' := by
        intro x
        change eFrac (eFrac.symm x) = x
        exact eFrac.apply_symm_apply x }
  let qRoot := tensorAlongFieldEquivCollapseIdeal
    (M := M) eBase
  let : qRoot.IsMaximal :=
    tensorAlongFieldEquivCollapseIdeal_isMaximal
      (M := M) eBase
  let Pq := GenericTensorFieldComponent qRoot
  let : Algebra C Pq :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) qRoot
  let : IsScalarTower E K Pq :=
    genericTensorFieldComponent_isScalarTower qRoot
  let eQ : Pq ≃ₐ[E] M :=
    tensorAlongFieldEquivCollapseComponentAlgEquiv
      (M := M) eBase
  let eQC : Pq ≃ₐ[C] M :=
    { toRingEquiv := eQ.toRingEquiv
      commutes' := by
        intro c
        change eQ
            (algebraMap K Pq
              (algebraMap E K (algebraMap C E c))) =
          algebraMap E M (algebraMap C E c)
        rw [← IsScalarTower.algebraMap_apply E K Pq]
        exact eQ.commutes (algebraMap C E c) }
  let eCollapseIC := eQC.symm.mapIntegralClosure
  let q₁ := q₀.map eCollapseIC.toRingEquiv
  let : q₁.IsPrime := by
    apply Ideal.map_isPrime_of_surjective eCollapseIC.surjective
    intro x hx
    have hx0 : x = 0 :=
      eCollapseIC.injective (hx.trans eCollapseIC.map_zero.symm)
    subst x
    exact q₀.zero_mem
  have hq₀comap : q₀ = q₁.comap eCollapseIC.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective
      eCollapseIC.toRingEquiv eCollapseIC.bijective
  let Ecollapse : Localization.AtPrime q₀ ≃ₐ[C]
      Localization.AtPrime q₁ :=
    Localization.localAlgEquiv q₀ q₁ eCollapseIC hq₀comap
  let n := genericTensorRefineChosenComponentIdeal
    (K₀ := K) (K₁ := E) (F := K) (L := L) m₀ qRoot
  let : n.IsMaximal :=
    genericTensorRefineChosenComponentIdeal_isMaximal
      (K₀ := K) (K₁ := E) (F := K) (L := L) m₀ qRoot
  let Pn := GenericTensorFieldComponent n
  let : Algebra C Pn :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) n
  let ErefIC :=
    genericTensorRefineChosenComponentIntegralClosureAlgEquiv
      (B := C) (K₀ := K) (K₁ := E) (F := K) (L := L)
      m₀ qRoot
  let p := q₁.comap ErefIC.toRingHom
  let : p.IsPrime := inferInstance
  let p' := genericTensorRefineChosenComponentIntegralClosurePrime
    (B := C) (K₀ := K) (K₁ := E) (F := K) (L := L)
    m₀ qRoot p
  let : p'.IsPrime :=
    genericTensorRefineChosenComponentIntegralClosurePrime_isPrime
      (B := C) (K₀ := K) (K₁ := E) (F := K) (L := L)
      m₀ qRoot p
  let Erefine : Localization.AtPrime p ≃ₐ[C]
      Localization.AtPrime p' :=
    genericTensorRefineChosenComponentIntegralClosureLocalizationAlgEquiv
      (B := C) (K₀ := K) (K₁ := E) (F := K) (L := L)
      m₀ qRoot p
  have hp' : p' = q₁ := by
    change (q₁.comap ErefIC.toRingHom).map ErefIC.toRingHom = q₁
    exact Ideal.map_comap_of_surjective
      ErefIC.toRingHom ErefIC.surjective q₁
  let Eprime : Localization.AtPrime p' ≃ₐ[C]
      Localization.AtPrime q₁ := by
    exact Localization.localAlgEquiv p' q₁ (AlgEquiv.refl :
      integralClosure C Pq ≃ₐ[C] integralClosure C Pq) (by
        change p' = q₁.comap (RingHom.id _)
        rw [Ideal.comap_id]
        exact hp')
  let Etotal : Localization.AtPrime q ≃ₐ[C]
      Localization.AtPrime p :=
    (Efield.trans Ecollapse).trans (Erefine.trans Eprime).symm
  exact ⟨⟨n, inferInstance⟩, ⟨⟨p, inferInstance⟩, ⟨Etotal⟩⟩⟩

end Kummer

end EtaleFundamentalGroups

end
