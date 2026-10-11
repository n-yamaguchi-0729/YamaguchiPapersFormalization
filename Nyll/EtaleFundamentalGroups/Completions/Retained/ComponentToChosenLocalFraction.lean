/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Retained.Component.LocalizationFractionRing

/-!
# A retained completed component as the chosen local fraction field

Let `N ≤ P` be a retained generic/closed-prime pair in a completed finite
model.  Once the localization at `P` has been source-produced as a domain,
the literal generic tensor component selected by `N` is its fraction field.
This file turns that intrinsic `IsFractionRing` statement into the canonical
equivalence with the standard `FractionRing` model.

The construction uses only the retained prime pair.  In particular, no
kernel equality, component comparison, or bijectivity hypothesis is exposed
to callers.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uR' uS uK uL uK'

variable {R : Type uR} {R' : Type uR'} {S : Type uS}
variable [CommRing R] [IsDomain R]
variable [CommRing R'] [IsDomain R'] [Algebra R R']
variable [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
variable {K' : Type uK'} [Field K'] [Algebra R' K']
variable [IsFractionRing R' K']
variable {K : Type uK} {L : Type uL}
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable [Algebra R L] [IsScalarTower R S L]
variable [Algebra K L] [IsScalarTower R K L]
variable [Algebra R K'] [IsScalarTower R R' K']
variable [Algebra K K'] [IsScalarTower R K K']

/-- The literal retained component selected by `N` is canonically
`R'`-equivalent to the standard fraction ring of any containing domain
localization.

The `W`-algebra structure on the component and its fraction-ring property
are both generated internally by
`retainedCompletedChosenComponentLocalization_isFractionRing`. -/
noncomputable def retainedCompletedComponentToChosenLocalFractionAlgEquiv
    (N P : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [P.IsPrime] (hNP : N ≤ P)
    [IsDomain (Localization.AtPrime P)] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Omega := GenericTensorFieldComponent m
    letI : Algebra R' Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    Omega ≃ₐ[R'] FractionRing (Localization.AtPrime P) := by
  classical
  dsimp only
  let T := R' ⊗[R] S
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
  let Omega := GenericTensorFieldComponent m
  let r'OmegaAlgebra : Algebra R' Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  letI : Algebra R' Omega := r'OmegaAlgebra
  letI : SMul R' Omega := r'OmegaAlgebra.toSMul
  letI : IsScalarTower R' K' Omega :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let W := Localization.AtPrime P
  let j := retainedCompletedChosenComponentAlgHom
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  letI : Algebra T Omega := j.toAlgebra
  letI : IsScalarTower R' T Omega :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (j.commutes x).symm
  letI : Algebra W Omega :=
    retainedCompletedChosenComponentLocalizationAlgebra
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N P hNP
  letI : IsScalarTower T W Omega :=
    retainedCompletedChosenComponentLocalization_isScalarTower
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N P hNP
  letI : IsFractionRing W Omega :=
    retainedCompletedChosenComponentLocalization_isFractionRing
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N P hNP
  letI : IsScalarTower R' T W :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower R' W Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply R' T Omega,
      IsScalarTower.algebraMap_apply R' T W,
      IsScalarTower.algebraMap_apply T W Omega]
  letI : IsScalarTower R' W (FractionRing W) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact (FractionRing.algEquiv W Omega).symm.restrictScalars R'

/-- The application-shaped injective map underlying
`retainedCompletedComponentToChosenLocalFractionAlgEquiv`.  This is the
form used to compose a retained lower-to-upper component embedding with the
chosen local fraction field. -/
theorem retainedCompletedComponentToChosenLocalFractionAlgHom_injective
    (N P : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')] [P.IsPrime] (hNP : N ≤ P)
    [IsDomain (Localization.AtPrime P)] :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Omega := GenericTensorFieldComponent m
    letI : Algebra R' Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    Function.Injective
      (retainedCompletedComponentToChosenLocalFractionAlgEquiv
        (R := R) (R' := R') (S := S) (K := K) (L := L)
        (K' := K') N P hNP).toAlgHom := by
  dsimp only
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let Omega := GenericTensorFieldComponent m
  let r'OmegaAlgebra : Algebra R' Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : Algebra R' Omega := r'OmegaAlgebra
  exact
    (retainedCompletedComponentToChosenLocalFractionAlgEquiv
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N P hNP).injective

end EtaleFundamentalGroups

end
