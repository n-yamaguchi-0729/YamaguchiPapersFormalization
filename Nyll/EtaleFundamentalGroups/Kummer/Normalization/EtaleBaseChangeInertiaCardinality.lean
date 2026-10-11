/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Smooth.IntegralClosure
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component
import Nyll.EtaleFundamentalGroups.Inertia.Localized.NormalCardinality
import Nyll.SchemeTheory.RingTheory.Ramification.Etale.SquareRamification

/-!
# Inertia cardinality after an arbitrary etale base change

This file treats an etale map which need not be finite.  A surjective
product map selects an actual compositum field.  Smooth base change for
integral closure makes the selected normalization etale over the original
normalization; a prime above the prescribed base prime can therefore be
compared by an etale ramification square.  Galois conjugacy removes the
dependence on which normalization prime occurs as its contraction.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uC uF uKC uL uM

/-- The product map into a field containing compatible copies of `C` and
`L`, regarded as a `C`-algebra homomorphism. -/
noncomputable def etaleBaseChangeProductMap
    {A : Type uA} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing A] [CommRing C] [Algebra A C]
    [CommRing L] [Algebra A L]
    [CommRing M] [Algebra A M] [Algebra C M] [Algebra L M]
    [IsScalarTower A C M] [IsScalarTower A L M] :
    C ⊗[A] L →ₐ[C] M :=
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId C M) (IsScalarTower.toAlgHom A L M)

/-- The canonical map from the old normalization to the normalization in
the selected compositum. -/
noncomputable def integralClosureEtaleBaseChangeHom
    {A : Type uA} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing A] [CommRing C] [Algebra A C]
    [CommRing L] [Algebra A L]
    [CommRing M] [Algebra A M] [Algebra C M] [Algebra L M]
    [IsScalarTower A C M] [IsScalarTower A L M] :
    integralClosure A L →+* integralClosure C M :=
  ((algebraMap L M).comp (integralClosure A L).val.toRingHom).codRestrict
    (integralClosure C M) fun x ↦
      ((x.2.map (IsScalarTower.toAlgHom A L M)).tower_top (A := C))

/-- The old normalization acts on the selected normalization through the
literal embedding `L → M`. -/
@[reducible]
noncomputable def integralClosureEtaleBaseChangeAlgebra
    {A : Type uA} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing A] [CommRing C] [Algebra A C]
    [CommRing L] [Algebra A L]
    [CommRing M] [Algebra A M] [Algebra C M] [Algebra L M]
    [IsScalarTower A C M] [IsScalarTower A L M] :
    Algebra (integralClosure A L) (integralClosure C M) :=
  integralClosureEtaleBaseChangeHom.toAlgebra

@[simp]
theorem integralClosureEtaleBaseChangeAlgebra_algebraMap_coe
    {A : Type uA} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing A] [CommRing C] [Algebra A C]
    [CommRing L] [Algebra A L]
    [CommRing M] [Algebra A M] [Algebra C M] [Algebra L M]
    [IsScalarTower A C M] [IsScalarTower A L M]
    (x : integralClosure A L) :
    letI : Algebra (integralClosure A L) (integralClosure C M) :=
      integralClosureEtaleBaseChangeAlgebra
    ((algebraMap (integralClosure A L) (integralClosure C M) x :
        integralClosure C M) : M) = algebraMap L M x.1 := by
  rfl

/-- Smooth integral closure identifies the normalization in a selected
compositum component with an idempotent etale factor of the tensor product
of the two normalizations.  In particular, the selected normalization is
etale over the old normalization even when `C / A` is not finite. -/
theorem integralClosure_etale_of_etaleBaseChangeProductMap_surjective
    {A : Type uA} {C : Type uC} {L : Type uL} {M : Type uM}
    [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C]
    [Field L] [Algebra A L]
    [Field M] [Algebra A M] [Algebra C M] [Algebra L M]
    [IsScalarTower A C M] [IsScalarTower A L M]
    (hproduct : Function.Surjective
      (etaleBaseChangeProductMap (A := A) (C := C) (L := L) (M := M))) :
    letI : Algebra (integralClosure A L) (integralClosure C M) :=
      integralClosureEtaleBaseChangeAlgebra
    Algebra.Etale (integralClosure A L) (integralClosure C M) := by
  classical
  let B := integralClosure A L
  let G := C ⊗[A] L
  let T := C ⊗[A] B
  let D := integralClosure C M
  let product : G →ₐ[C] M :=
    etaleBaseChangeProductMap (A := A) (C := C) (L := L) (M := M)
  let : Algebra L G := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A L G :=
    Algebra.TensorProduct.right_isScalarTower
  let commL : (L ⊗[A] C) ≃ₐ[L] G :=
    Algebra.TensorProduct.commRight A L C
  let : Algebra.Etale L G := Algebra.Etale.of_equiv commL
  let : Module.Finite L G :=
    Algebra.FormallyUnramified.finite_of_free L G
  let : IsArtinianRing G := isArtinian_of_tower L inferInstance
  let : IsReduced G :=
    Algebra.FormallyUnramified.isReduced_of_field L G
  let m : Ideal G := RingHom.ker product.toRingHom
  let : m.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective product hproduct
  let Omega := G ⧸ m
  let : Field Omega := Ideal.Quotient.field m
  let eOmega : Omega ≃ₐ[C] M :=
    Ideal.quotientKerAlgEquivOfSurjective hproduct
  let : Algebra B D := integralClosureEtaleBaseChangeAlgebra
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower A B T :=
    Algebra.TensorProduct.right_isScalarTower
  let qOmega : G →ₐ[C] Omega := Ideal.Quotient.mkₐ C m
  let compare : T →ₐ[C] integralClosure C G :=
    TensorProduct.toIntegralClosure A C L
  let componentMapC : T →ₐ[C] D :=
    eOmega.mapIntegralClosure.toAlgHom.comp
      (qOmega.mapIntegralClosure.comp compare)
  have hcomponentMapC_right (b : B) :
      componentMapC (1 ⊗ₜ[A] b) = algebraMap B D b := by
    apply Subtype.ext
    change product (1 ⊗ₜ[A] (b.1 : L)) = algebraMap L M b.1
    change
      (Algebra.ofId C M) 1 *
          (IsScalarTower.toAlgHom A L M) b.1 =
        algebraMap L M b.1
    simp
  let componentMap : T →ₐ[B] D :=
    { toRingHom := componentMapC.toRingHom
      commutes' := hcomponentMapC_right }
  have hcompare : Function.Bijective compare :=
    TensorProduct.toIntegralClosure_bijective_of_smooth
      (R := A) (S := C) (B := L)
  have hcomponentMap_surjective : Function.Surjective componentMap := by
    intro x
    let xOmega : integralClosure C Omega :=
      eOmega.mapIntegralClosure.symm x
    obtain ⟨y, hy, hym⟩ :=
      exists_integral_artinianElement_supported_at_component
        (R := C) m xOmega.1 xOmega.2
    obtain ⟨z, hz⟩ := hcompare.2 ⟨y, hy⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change eOmega (Ideal.Quotient.mk m (compare z).1) = x.1
    rw [hz, hym]
    exact congrArg Subtype.val
      (eOmega.mapIntegralClosure.apply_symm_apply x)
  let eG : G := artinianSelectedComponentIdempotent m
  have heG : IsIdempotentElem eG :=
    artinianSelectedComponentIdempotent_isIdempotentElem m
  have heG_integral : IsIntegral C eG := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1),
      Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    change Polynomial.aeval eG
      (Polynomial.X * (Polynomial.X - Polynomial.C 1)) = 0
    rw [map_mul, Polynomial.aeval_X, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, map_one]
    rw [mul_sub, mul_one, heG.eq, sub_self]
  obtain ⟨eT, heT_image⟩ := hcompare.2 ⟨eG, heG_integral⟩
  have heT : IsIdempotentElem eT := by
    apply hcompare.1
    rw [map_mul, heT_image]
    apply Subtype.ext
    exact heG.eq
  have hcomponentMap_eq_zero_iff (z : T) :
      componentMap z = (0 : D) ↔ eT * z = 0 := by
    rw [Subtype.ext_iff]
    change eOmega
        (Ideal.Quotient.mk m (compare z).1) = 0 ↔ _
    rw [← map_zero eOmega, eOmega.injective.eq_iff]
    rw [← artinianSelectedComponentIdempotent_mul_eq_zero_iff m]
    change eG * (compare z).1 = 0 ↔ eT * z = 0
    constructor
    · intro hz
      apply hcompare.1
      rw [map_mul, map_zero, heT_image]
      apply Subtype.ext
      change eG * (compare z).1 = 0
      exact hz
    · intro hz
      have hcz : compare (eT * z) = compare 0 := congrArg compare hz
      rw [map_mul, map_zero, heT_image] at hcz
      have hczVal := congrArg Subtype.val hcz
      change eG * (compare z).1 = 0 at hczVal
      exact hczVal
  have hcomponentMap_mul_iff (x y : T) :
      componentMap x = componentMap y ↔ eT * x = eT * y := by
    calc
      componentMap x = componentMap y ↔
          componentMap (x - y) = (0 : D) := by
            rw [map_sub, sub_eq_zero]
      _ ↔ eT * (x - y) = 0 := hcomponentMap_eq_zero_iff (x - y)
      _ ↔ eT * x = eT * y := by rw [mul_sub, sub_eq_zero]
  let : Algebra T D := componentMap.toAlgebra
  let : IsScalarTower B T D := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    exact (hcomponentMapC_right b).symm
  let : IsLocalization.Away eT D :=
    IsLocalization.away_of_isIdempotentElem_of_mul
      heT hcomponentMap_mul_iff hcomponentMap_surjective
  let : Algebra.Etale T D := Algebra.Etale.of_isLocalizationAway eT
  let commB : (B ⊗[A] C) ≃ₐ[B] T :=
    Algebra.TensorProduct.commRight A B C
  let : Algebra.Etale B T := Algebra.Etale.of_equiv commB
  exact Algebra.Etale.comp B T D

end EtaleFundamentalGroups

end
