/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ChosenPrime.LocalFactor
import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# Field-tensor coordinates for an actual chosen generic component

Let `C / R` be finite and let `L` be a field over the fraction field of
`R`.  The literal generic algebra `C ⊗[R] L` is canonically the field
tensor product

`FractionRing C ⊗[FractionRing R] L`.

This file transports a specified maximal component, a normalization prime,
and its prime localization across that canonical comparison.  In
particular, a component produced by `EtaleChosenPrimeLocalFactor` is not
reselected after passing to fraction fields.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uC uL

variable {R : Type uR} {C : Type uC} {L : Type uL}
variable [CommRing R] [IsDomain R]
variable [CommRing C] [IsDomain C]
variable [Algebra R C] [FaithfulSMul R C]
variable [Field L] [Algebra R L]
variable [Algebra (FractionRing R) L]

/-- The fraction-field extension induced by a faithful finite map
`R → C`. -/
@[reducible]
noncomputable def finiteBaseFractionRingAlgebra :
    Algebra (FractionRing R) (FractionRing C) := by
  letI : FaithfulSMul R (FractionRing C) :=
    FaithfulSMul.trans R C (FractionRing C)
  exact FractionRing.liftAlgebra R (FractionRing C)

local instance finiteBaseFractionRingAlgebraInstance :
    Algebra (FractionRing R) (FractionRing C) :=
  finiteBaseFractionRingAlgebra (R := R) (C := C)

/-- The scalar action of `C` on the field tensor product is the literal
left-factor action through `FractionRing C`. -/
@[reducible]
noncomputable def finiteBaseFractionFieldTensorAlgebra :
    let K := FractionRing R
    let E := FractionRing C
    Algebra C (E ⊗[K] L) := by
  dsimp only
  exact genericTensorProductLeftScalarAlgebra
    (R := C) (K := FractionRing R) (F := FractionRing C) (L := L)

/-- Canonical comparison between the literal finite generic fibre and the
tensor product of the two fraction fields.

It is linear over `C`: on the target, `C` acts through the left copy of
`FractionRing C`. -/
noncomputable def finiteBaseFractionFieldTensorAlgEquiv
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L] :
    let K := FractionRing R
    let E := FractionRing C
    letI : Algebra C (E ⊗[K] L) :=
      finiteBaseFractionFieldTensorAlgebra (R := R) (C := C) (L := L)
    (C ⊗[R] L) ≃ₐ[C] (E ⊗[K] L) := by
  dsimp only
  let K := FractionRing R
  let E := FractionRing C
  letI : IsScalarTower R K E :=
    FractionRing.isScalarTower_liftAlgebra R E
  letI : Algebra C (E ⊗[K] L) :=
    finiteBaseFractionFieldTensorAlgebra (R := R) (C := C) (L := L)
  letI : Algebra L (C ⊗[R] L) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (E ⊗[K] L) :=
    Algebra.TensorProduct.rightAlgebra
  let eGeneric : (K ⊗[R] C) ≃ₐ[K] E :=
    finiteGenericFiberAlgEquiv
      (R := R) (C := C) (K := K) (E := E)
  let eL : (C ⊗[R] L) ≃ₐ[L] (E ⊗[K] L) :=
    (Algebra.TensorProduct.commRight R L C).symm |>.trans
      (iteratedGenericFiberEquiv R K L C E eGeneric) |>.trans
      (Algebra.TensorProduct.commRight K L E)
  refine
    { toRingEquiv := eL.toRingEquiv
      commutes' := ?_ }
  intro c
  change eL (c ⊗ₜ[R] (1 : L)) =
    (algebraMap C E c) ⊗ₜ[K] (1 : L)
  simp [eL, eGeneric, iteratedGenericFiberEquiv]

/-- The literal maximal ideal of the fraction-field tensor product obtained
from the already selected component of `C ⊗[R] L`. -/
noncomputable def finiteBaseFractionFieldTensorIdeal
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) :
    Ideal ((FractionRing C) ⊗[FractionRing R] L) := by
  letI : Algebra C
      ((FractionRing C) ⊗[FractionRing R] L) :=
    finiteBaseFractionFieldTensorAlgebra (R := R) (C := C) (L := L)
  exact m.map
    (finiteBaseFractionFieldTensorAlgEquiv
      (R := R) (C := C) (L := L)).toRingEquiv

/-- The transported fraction-field tensor ideal is maximal. -/
theorem finiteBaseFractionFieldTensorIdeal_isMaximal
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal] :
    (finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m).IsMaximal := by
  let : Algebra C
      ((FractionRing C) ⊗[FractionRing R] L) :=
    finiteBaseFractionFieldTensorAlgebra (R := R) (C := C) (L := L)
  exact (inferInstance : m.IsMaximal).map_bijective
    (finiteBaseFractionFieldTensorAlgEquiv
      (R := R) (C := C) (L := L)).toRingEquiv.toRingHom
    (finiteBaseFractionFieldTensorAlgEquiv
      (R := R) (C := C) (L := L)).bijective

/-- The actual quotient component produced before fieldification is
canonically the literal generic tensor component after fieldification. -/
noncomputable def finiteBaseFractionFieldTensorComponentAlgEquiv
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal] :
    let n := finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m
    letI : n.IsMaximal :=
      finiteBaseFractionFieldTensorIdeal_isMaximal
        (R := R) (C := C) (L := L) m
    letI : Algebra C (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) n
    FiniteEtaleGenericFiberComponent m ≃ₐ[C]
      GenericTensorFieldComponent n := by
  dsimp only
  let T := (FractionRing C) ⊗[FractionRing R] L
  letI : Algebra C T :=
    finiteBaseFractionFieldTensorAlgebra (R := R) (C := C) (L := L)
  let E : (C ⊗[R] L) ≃ₐ[C] T :=
    finiteBaseFractionFieldTensorAlgEquiv
      (R := R) (C := C) (L := L)
  let n : Ideal T := finiteBaseFractionFieldTensorIdeal
    (R := R) (C := C) (L := L) m
  letI : n.IsMaximal :=
    finiteBaseFractionFieldTensorIdeal_isMaximal
      (R := R) (C := C) (L := L) m
  letI : Algebra C (GenericTensorFieldComponent n) :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) n
  let qE : ((C ⊗[R] L) ⧸ m) ≃+* (T ⧸ n) :=
    Ideal.quotientEquiv m n E.toRingEquiv rfl
  exact AlgEquiv.ofRingEquiv (f := qE) fun c ↦ by
    change qE (Ideal.Quotient.mk m
      (algebraMap C (C ⊗[R] L) c)) =
        algebraMap C (T ⧸ n) c
    dsimp only [qE]
    rw [Ideal.quotientEquiv_mk m n E.toRingEquiv rfl]
    exact congrArg (Ideal.Quotient.mk n) (E.commutes c)

/-- Integral closures in the two presentations of the same actual component
are canonically equivalent. -/
noncomputable def finiteBaseFractionFieldTensorIntegralClosureAlgEquiv
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal] :
    let n := finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m
    letI : n.IsMaximal :=
      finiteBaseFractionFieldTensorIdeal_isMaximal
        (R := R) (C := C) (L := L) m
    letI : Algebra C (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) n
    integralClosure C (FiniteEtaleGenericFiberComponent m) ≃ₐ[C]
      integralClosure C (GenericTensorFieldComponent n) := by
  dsimp only
  let n := finiteBaseFractionFieldTensorIdeal
    (R := R) (C := C) (L := L) m
  letI : n.IsMaximal :=
    finiteBaseFractionFieldTensorIdeal_isMaximal
      (R := R) (C := C) (L := L) m
  letI : Algebra C (GenericTensorFieldComponent n) :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) n
  let E := finiteBaseFractionFieldTensorComponentAlgEquiv
    (R := R) (C := C) (L := L) m
  exact E.mapIntegralClosure

/-- The normalization prime obtained by literal transport to the
fraction-field tensor component. -/
noncomputable def finiteBaseFractionFieldTensorIntegralClosurePrime
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal]
    (q : Ideal (integralClosure C
      (FiniteEtaleGenericFiberComponent m))) :
    let n := finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m
    letI : n.IsMaximal :=
      finiteBaseFractionFieldTensorIdeal_isMaximal
        (R := R) (C := C) (L := L) m
    letI : Algebra C (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) n
    Ideal (integralClosure C (GenericTensorFieldComponent n)) := by
  dsimp only
  exact q.map
    (finiteBaseFractionFieldTensorIntegralClosureAlgEquiv
      (R := R) (C := C) (L := L) m).toRingEquiv

/-- Literal transport of a normalization prime preserves primality. -/
theorem finiteBaseFractionFieldTensorIntegralClosurePrime_isPrime
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal]
    (q : Ideal (integralClosure C
      (FiniteEtaleGenericFiberComponent m))) [q.IsPrime] :
    let n := finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m
    letI : n.IsMaximal :=
      finiteBaseFractionFieldTensorIdeal_isMaximal
        (R := R) (C := C) (L := L) m
    letI : Algebra C (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) n
    (finiteBaseFractionFieldTensorIntegralClosurePrime
      (R := R) (C := C) (L := L) m q).IsPrime := by
  dsimp only
  let E := finiteBaseFractionFieldTensorIntegralClosureAlgEquiv
    (R := R) (C := C) (L := L) m
  apply Ideal.map_isPrime_of_surjective E.surjective
  intro x hx
  have hx0 : x = 0 := E.injective (hx.trans (map_zero E).symm)
  subst x
  exact q.zero_mem

/-- Prime localization of the actual chosen component is unchanged by the
canonical field-tensor presentation. -/
noncomputable def
    finiteBaseFractionFieldTensorIntegralClosureLocalizationAlgEquiv
    [Module.Finite R C]
    [IsScalarTower R (FractionRing R) L]
    (m : Ideal (C ⊗[R] L)) [m.IsMaximal]
    (q : Ideal (integralClosure C
      (FiniteEtaleGenericFiberComponent m))) [q.IsPrime] :
    let n := finiteBaseFractionFieldTensorIdeal
      (R := R) (C := C) (L := L) m
    letI : n.IsMaximal :=
      finiteBaseFractionFieldTensorIdeal_isMaximal
        (R := R) (C := C) (L := L) m
    letI : Algebra C (GenericTensorFieldComponent n) :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) n
    let q' := finiteBaseFractionFieldTensorIntegralClosurePrime
      (R := R) (C := C) (L := L) m q
    letI : q'.IsPrime :=
      finiteBaseFractionFieldTensorIntegralClosurePrime_isPrime
        (R := R) (C := C) (L := L) m q
    Localization.AtPrime q ≃ₐ[C] Localization.AtPrime q' := by
  dsimp only
  let E := finiteBaseFractionFieldTensorIntegralClosureAlgEquiv
    (R := R) (C := C) (L := L) m
  let q' := finiteBaseFractionFieldTensorIntegralClosurePrime
    (R := R) (C := C) (L := L) m q
  letI : q'.IsPrime :=
    finiteBaseFractionFieldTensorIntegralClosurePrime_isPrime
      (R := R) (C := C) (L := L) m q
  have hcomap : q = q'.comap E.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective E.toRingEquiv E.bijective
  exact Localization.localAlgEquiv q q' E hcomap

end EtaleFundamentalGroups

end
