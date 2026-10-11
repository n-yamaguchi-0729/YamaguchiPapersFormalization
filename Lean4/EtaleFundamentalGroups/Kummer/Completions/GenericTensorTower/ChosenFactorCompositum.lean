/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.ActualCompositumComponent
import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.IntegralClosureBaseChange
import EtaleFundamentalGroups.Normalization.IntegralClosure.Localization.FractionFieldComparison
import EtaleFundamentalGroups.Kummer.GenericTensor.Tower.Intermediate.NormalizationClosedPrime

/-!
# The prefix compositum inside a chosen final localization

Fix a literal component `m` of a two-step generic tensor tower and a prime
`p` of the normalization of its final component.  The contraction of `p`
selects the canonical intermediate component, while localization at `p`
has fraction field canonically equivalent to the original final component.

This file combines those two source constructions.  It embeds the literal
intermediate component into the fraction ring of the chosen localization,
first over the integral base and then over its fraction field.  After a
finite residue extension it also records the actual compositum component
selected by the two embeddings in that same fraction ring.  No comparison
between independently chosen factors, right-coordinate bijectivity, or
degree equality is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uA uB uK uF uF' uL uP

open DiscreteValuationField.FieldCompositum

/-- The actual-compositum component map retains the literal coordinate of
its left (base-change) tensor factor.  This is the companion to the existing
right-factor formula and is used to make the pulled-back `KC` component act
on the chosen ambient fraction field. -/
@[simp]
theorem actualCompositumGenericComponentMap_tmul_left_coe
    {R T F P : Type*}
    [CommRing R] [CommRing T] [Algebra R T]
    [Field F] [Algebra R F]
    [Field P] [Algebra F P]
    (E K' : IntermediateField F P)
    [Algebra R K'] [IsScalarTower R F K']
    (eGeneric : (F ⊗[R] T) ≃ₐ[F] E) (x : K') :
    (((actualCompositumGenericComponentMap E K' eGeneric)
        (x ⊗ₜ[R] (1 : T)) :
          (E ⊔ K' : IntermediateField F P)) : P) = x := by
  change
    (((actualCompositumGenericComponentMap E K' eGeneric)
        (algebraMap K' (K' ⊗[R] T) x) :
          (E ⊔ K' : IntermediateField F P)) : P) = x
  rw [(actualCompositumGenericComponentMap E K' eGeneric).commutes]
  rfl

/-- An algebra map over a domain extends uniquely to linearity over a chosen
fraction field, provided both target actions form the corresponding scalar
towers. -/
noncomputable def fractionFieldBaseAlgHomOfRestrictScalars
    {A : Type uA} {F : Type uF} {E : Type uK} {P : Type uP}
    [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra A E] [Algebra F E] [IsScalarTower A F E]
    [Field P] [Algebra A P] [Algebra F P] [IsScalarTower A F P]
    (f : E →ₐ[A] P) : E →ₐ[F] P :=
  { f.toRingHom with
    commutes' := by
      intro x
      have hmaps :
          f.toRingHom.comp (algebraMap F E) = algebraMap F P := by
        apply IsFractionRing.ringHom_ext (A := A)
        intro a
        calc
          f (algebraMap F E (algebraMap A F a)) =
              f (algebraMap A E a) := by
                rw [IsScalarTower.algebraMap_apply A F E]
          _ = algebraMap A P a := f.commutes a
          _ = algebraMap F P (algebraMap A F a) :=
            IsScalarTower.algebraMap_apply A F P a
      exact DFunLike.congr_fun hmaps x }

/-- Two fraction-field lifts into a common target field are compatible when
their integral-base maps are compatible.  This is the scalar-tower source
used after passing from a complete local base to its finite residue lift. -/
theorem fractionFieldTower_of_common_integral_base
    {A : Type uA} {C : Type uB} {F : Type uF} {KC : Type uF'}
    {P : Type uP}
    [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field P] [Algebra A P] [Algebra C P] [IsScalarTower A C P]
    [Algebra F P] [IsScalarTower A F P]
    [Algebra KC P] [IsScalarTower C KC P] :
    IsScalarTower F KC P := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  have hmaps :
      (algebraMap KC P).comp (algebraMap F KC) = algebraMap F P := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    calc
      algebraMap KC P (algebraMap F KC (algebraMap A F a)) =
          algebraMap KC P (algebraMap A KC a) := by
        rw [IsScalarTower.algebraMap_apply A F KC]
      _ = algebraMap KC P (algebraMap C KC (algebraMap A C a)) := by
        rw [IsScalarTower.algebraMap_apply A C KC]
      _ = algebraMap C P (algebraMap A C a) :=
        (IsScalarTower.algebraMap_apply C KC P _).symm
      _ = algebraMap A P a :=
        (IsScalarTower.algebraMap_apply A C P a).symm
      _ = algebraMap F P (algebraMap A F a) :=
        IsScalarTower.algebraMap_apply A F P a
  exact (DFunLike.congr_fun hmaps x).symm

section ChosenLocalization

variable {A : Type uA} {B : Type uB}
variable {K : Type uK} {F : Type uF} {F' : Type uF'} {L : Type uL}
variable [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Field K] [Field F] [Field F'] [Field L]
variable [Algebra K F] [Algebra F F'] [Algebra K F']
variable [IsScalarTower K F F'] [Algebra K L]
variable [Algebra A F] [IsFractionRing A F]
variable [Algebra A F'] [IsScalarTower A F F']
variable [Algebra A B] [Algebra.IsIntegral A B]
variable [Algebra B F'] [IsFractionRing B F']
variable [IsScalarTower A B F']

/-- The canonical embedding of the intermediate tensor component into the
fraction ring of the chosen localization of the final normalization.

The algebra structures on the normalization localization and its fraction
ring are the literal composites from `A → B`; the comparison with the final
component is the canonical integral-closure localization equivalence.  The
finite-dimensionality of `L / K` is what makes that final component finite
over `F'`, hence the fraction field of its normalization. -/
noncomputable def
    genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom
    [FiniteDimensional K L] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsPrime] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    let M := GenericTensorFieldComponent m
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    letI : SMul A M₀ :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := A) n).toSMul
    letI : Algebra A M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) m
    letI : SMul A M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : SMul B M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
    let E := integralClosure B M
    let D := Localization.AtPrime p
    let bDAlgebra : Algebra B D :=
      ((algebraMap E D).comp (algebraMap B E)).toAlgebra
    letI : Algebra B D := bDAlgebra
    letI : SMul B D := bDAlgebra.toSMul
    let aDAlgebra : Algebra A D :=
      ((algebraMap B D).comp (algebraMap A B)).toAlgebra
    letI : Algebra A D := aDAlgebra
    letI : SMul A D := aDAlgebra.toSMul
    let P := FractionRing D
    let bPAlgebra : Algebra B P :=
      ((algebraMap D P).comp (algebraMap B D)).toAlgebra
    letI : Algebra B P := bPAlgebra
    letI : SMul B P := bPAlgebra.toSMul
    let aPAlgebra : Algebra A P :=
      ((algebraMap B P).comp (algebraMap A B)).toAlgebra
    letI : Algebra A P := aPAlgebra
    letI : SMul A P := aPAlgebra.toSMul
    M₀ →ₐ[A] P := by
  dsimp only at p ⊢
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let M := GenericTensorFieldComponent m
  letI : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  letI : SMul A M₀ :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) n).toSMul
  letI : Algebra A M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) m
  letI : SMul A M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI : SMul B M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
  letI : SMul F' M := (inferInstance : Algebra F' M).toSMul
  letI : IsScalarTower B F' M :=
    @IsScalarTower.of_algebraMap_eq B F' M _ _ _ _ _ _ fun _ ↦ rfl
  letI : IsScalarTower A B M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change
      genericTensorFieldComponentLeft m (algebraMap A F' x) =
        genericTensorFieldComponentLeft m
          (algebraMap B F' (algebraMap A B x))
    rw [IsScalarTower.algebraMap_apply A B F']
  let E := integralClosure B M
  let D := Localization.AtPrime p
  let bDAlgebra : Algebra B D :=
    ((algebraMap E D).comp (algebraMap B E)).toAlgebra
  letI : Algebra B D := bDAlgebra
  letI : SMul B D := bDAlgebra.toSMul
  letI : SMul E D := (inferInstance : Algebra E D).toSMul
  letI : IsScalarTower B E D := IsScalarTower.of_algebraMap_eq' rfl
  let aDAlgebra : Algebra A D :=
    ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  letI : Algebra A D := aDAlgebra
  letI : SMul A D := aDAlgebra.toSMul
  letI : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  let P := FractionRing D
  let bPAlgebra : Algebra B P :=
    ((algebraMap D P).comp (algebraMap B D)).toAlgebra
  letI : Algebra B P := bPAlgebra
  letI : SMul B P := bPAlgebra.toSMul
  letI : SMul D P := (inferInstance : Algebra D P).toSMul
  letI : IsScalarTower B D P := IsScalarTower.of_algebraMap_eq' rfl
  let aPAlgebra : Algebra A P :=
    ((algebraMap B P).comp (algebraMap A B)).toAlgebra
  letI : Algebra A P := aPAlgebra
  letI : SMul A P := aPAlgebra.toSMul
  letI : IsScalarTower A B P := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing E M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B F' M E
  letI : SMul E M := (inferInstance : Algebra E M).toSMul
  letI : IsScalarTower B E M :=
    @IsScalarTower.of_algebraMap_eq B E M _ _ _ _ _ _ fun _ ↦ rfl
  letI : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) p
  letI : SMul D M :=
    (localizationAtPrimeToFractionFieldAlgebra (K := M) p).toSMul
  letI : IsScalarTower E D M :=
    localizationAtPrimeToFractionField_isScalarTower (K := M) p
  letI : IsScalarTower B D M := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap B M z = algebraMap E M (algebraMap B E z) :=
        IsScalarTower.algebraMap_apply B E M z
      _ = algebraMap D M (algebraMap E D (algebraMap B E z)) :=
        IsScalarTower.algebraMap_apply E D M _
      _ = algebraMap D M (algebraMap B D z) := by
        rw [IsScalarTower.algebraMap_apply B E D]
  let eDM : P ≃ₐ[D] M :=
    integralClosureLocalizationFractionRingAlgEquiv
      (B := B) (K := F') (M := M) p
  let eA : P ≃ₐ[A] M :=
    { toRingEquiv := eDM.toRingEquiv
      commutes' := by
        intro z
        change eDM
            (algebraMap D P
              (algebraMap B D (algebraMap A B z))) =
          algebraMap A M z
        rw [eDM.commutes]
        calc
          algebraMap D M (algebraMap B D (algebraMap A B z)) =
              algebraMap B M (algebraMap A B z) :=
            (IsScalarTower.algebraMap_apply B D M _).symm
          _ = algebraMap A M z :=
            (IsScalarTower.algebraMap_apply A B M z).symm }
  let f : M₀ →ₐ[A] M :=
    genericTensorTowerIntermediateComponentAlgHomRestrictBase
      (A := A) (K := K) (F := F) (F' := F') (L := L) m
  exact eA.symm.toAlgHom.comp f

omit [IsDomain A] [IsFractionRing A F] [Algebra.IsIntegral A B] in
/-- The chosen-localization embedding is injective; this is a consequence of
its construction as a composite of field embeddings. -/
theorem
    genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom_injective
    [FiniteDimensional K L] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsPrime] :
    Function.Injective
      (genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom
        (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
        m p) := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  exact
    (genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p).injective

/-- The same canonical embedding, strengthened from `A`-linearity to
`Frac(A)`-linearity.  The action of `F` on the chosen localization fraction
ring is not supplied: it is the unique fraction-field lift of its produced
`A`-action. -/
noncomputable def
    genericTensorTowerIntermediateComponentToChosenLocalizationFractionAlgHom
    [FiniteDimensional K L] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsPrime] :
    let n := genericTensorTowerIntermediateIdeal
      (K := K) (F := F) (F' := F') (L := L) m
    letI : n.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := F) (F' := F') (L := L) m
    let M₀ := GenericTensorFieldComponent n
    let M := GenericTensorFieldComponent m
    letI : Algebra A M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) n
    letI : SMul A M₀ :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := A) n).toSMul
    letI : Algebra A M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := A) m
    letI : SMul A M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : SMul B M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
    let E := integralClosure B M
    let D := Localization.AtPrime p
    let bDAlgebra : Algebra B D :=
      ((algebraMap E D).comp (algebraMap B E)).toAlgebra
    letI : Algebra B D := bDAlgebra
    letI : SMul B D := bDAlgebra.toSMul
    let aDAlgebra : Algebra A D :=
      ((algebraMap B D).comp (algebraMap A B)).toAlgebra
    letI : Algebra A D := aDAlgebra
    letI : SMul A D := aDAlgebra.toSMul
    let P := FractionRing D
    let bPAlgebra : Algebra B P :=
      ((algebraMap D P).comp (algebraMap B D)).toAlgebra
    letI : Algebra B P := bPAlgebra
    letI : SMul B P := bPAlgebra.toSMul
    let aPAlgebra : Algebra A P :=
      ((algebraMap B P).comp (algebraMap A B)).toAlgebra
    letI : Algebra A P := aPAlgebra
    letI : SMul A P := aPAlgebra.toSMul
    let fA : M₀ →ₐ[A] P :=
      genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom
        (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
        m p
    letI : FaithfulSMul A P :=
      (faithfulSMul_iff_algebraMap_injective A P).mpr <| by
        intro x y hxy
        apply FaithfulSMul.algebraMap_injective A F
        apply (genericTensorFieldComponentLeft n).injective
        apply fA.injective
        change fA (algebraMap A M₀ x) = fA (algebraMap A M₀ y)
        rw [fA.commutes x, fA.commutes y, hxy]
    let fPAlgebra : Algebra F P :=
      (IsFractionRing.lift
        (FaithfulSMul.algebraMap_injective A P)).toAlgebra
    letI : Algebra F P := fPAlgebra
    letI : SMul F P := fPAlgebra.toSMul
    letI : IsScalarTower A F P := IsScalarTower.of_algebraMap_eq fun x ↦
      (IsFractionRing.lift_algebraMap
        (FaithfulSMul.algebraMap_injective A P) x).symm
    M₀ →ₐ[F] P := by
  dsimp only at p ⊢
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  letI : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let M₀ := GenericTensorFieldComponent n
  let M := GenericTensorFieldComponent m
  letI : Algebra A M₀ :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) n
  letI : SMul A M₀ :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) n).toSMul
  letI : SMul F M₀ := (inferInstance : Algebra F M₀).toSMul
  letI : Algebra A M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := A) m
  letI : SMul A M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := A) m).toSMul
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI : SMul B M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
  letI : IsScalarTower A F M₀ :=
    @IsScalarTower.of_algebraMap_eq A F M₀ _ _ _ _ _ _ fun _ ↦ rfl
  let E := integralClosure B M
  let D := Localization.AtPrime p
  let bDAlgebra : Algebra B D :=
    ((algebraMap E D).comp (algebraMap B E)).toAlgebra
  letI : Algebra B D := bDAlgebra
  letI : SMul B D := bDAlgebra.toSMul
  let aDAlgebra : Algebra A D :=
    ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  letI : Algebra A D := aDAlgebra
  letI : SMul A D := aDAlgebra.toSMul
  let P := FractionRing D
  let bPAlgebra : Algebra B P :=
    ((algebraMap D P).comp (algebraMap B D)).toAlgebra
  letI : Algebra B P := bPAlgebra
  letI : SMul B P := bPAlgebra.toSMul
  let aPAlgebra : Algebra A P :=
    ((algebraMap B P).comp (algebraMap A B)).toAlgebra
  letI : Algebra A P := aPAlgebra
  letI : SMul A P := aPAlgebra.toSMul
  let fA : M₀ →ₐ[A] P :=
    genericTensorTowerIntermediateComponentToChosenLocalizationAlgHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p
  letI : FaithfulSMul A P :=
    (faithfulSMul_iff_algebraMap_injective A P).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective A F
      apply (genericTensorFieldComponentLeft n).injective
      apply fA.injective
      change fA (algebraMap A M₀ x) = fA (algebraMap A M₀ y)
      rw [fA.commutes x, fA.commutes y, hxy]
  let fPAlgebra : Algebra F P :=
    (IsFractionRing.lift
      (FaithfulSMul.algebraMap_injective A P)).toAlgebra
  letI : Algebra F P := fPAlgebra
  letI : SMul F P := fPAlgebra.toSMul
  letI : IsScalarTower A F P := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A P) x).symm
  exact fractionFieldBaseAlgHomOfRestrictScalars fA

omit [Algebra.IsIntegral A B] in
/-- The fraction-field-strengthened chosen-localization embedding remains
injective. -/
theorem
    genericTensorTowerIntermediateComponentToChosenLocalizationFractionAlgHom_injective
    [FiniteDimensional K L] [FiniteDimensional F F']
    (m : Ideal (F' ⊗[K] L)) [m.IsMaximal]
    (p :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M)) [p.IsPrime] :
    Function.Injective
      (genericTensorTowerIntermediateComponentToChosenLocalizationFractionAlgHom
        (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
        m p) := by
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  exact
    (genericTensorTowerIntermediateComponentToChosenLocalizationFractionAlgHom
      (A := A) (B := B) (K := K) (F := F) (F' := F') (L := L)
      m p).injective

end ChosenLocalization

end EtaleFundamentalGroups.Kummer

end
