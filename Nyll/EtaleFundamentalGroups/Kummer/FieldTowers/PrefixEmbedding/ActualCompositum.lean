/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.GenericTensorTower.ChosenFactorCompositum
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# A field prefix embedded in a common ambient compositum

An embedding of a finite Galois prefix field `M/K` into a field `P` which
also contains a field extension `F/K` determines one literal component of
`F tensor[K] M`.  This file exposes that component and its embedding back
into `P`, retaining both tensor coordinates.  It is the noetherian-free
field-level junction used before a completed chosen factor is passed to the
finite residue-lift compositum construction.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- A concrete prefix embedding selects the literal base-change component
inside the same ambient field.

The ideal is the pullback of the kernel of the actual-compositum product
map.  The returned map is therefore injective and its left and right
coordinate formulas are definitional consequences of that product map,
not comparison assumptions. -/
theorem fieldPrefixEmbedding_actualCompositum
    {K F M P : Type u}
    [Field K] [Field F] [Field M] [Field P]
    [Algebra K F] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    [Algebra K P] [Algebra F P] [IsScalarTower K F P]
    (fPrefix : M →ₐ[K] P) :
    let fF : F →ₐ[K] P := IsScalarTower.toAlgHom K F P
    let Eimage : IntermediateField K P := fPrefix.fieldRange
    let Fimage : IntermediateField K P := fF.fieldRange
    let hfiniteEimage : FiniteDimensional K Eimage :=
      fPrefix.toLinearMap.finiteDimensional_range
    letI : FiniteDimensional K Eimage := hfiniteEimage
    let eGeneric : (K ⊗[K] M) ≃ₐ[K] Eimage :=
      (Algebra.TensorProduct.lid K M).trans fPrefix.equivFieldRange
    let mActual := actualCompositumGenericComponentIdeal
      (A := K) (T := M) (F := K) (Omega := P)
      Eimage Fimage eGeneric
    let hmActual : mActual.IsMaximal :=
      actualCompositumGenericComponentIdeal_isMaximal
        Eimage Fimage eGeneric
    let eF : F ≃ₐ[K] Fimage := fF.equivFieldRange
    let eTensorF : (F ⊗[K] M) ≃ₐ[K] (Fimage ⊗[K] M) :=
      Algebra.TensorProduct.congr eF (AlgEquiv.refl : M ≃ₐ[K] M)
    let mF := mActual.comap eTensorF.toRingEquiv.toRingHom
    let hmF : mF.IsMaximal :=
      hmActual.comap_bijective eTensorF.toRingEquiv.toRingHom
        eTensorF.bijective
    letI : mF.IsMaximal := hmF
    let Omega := GenericTensorFieldComponent mF
    ∃ omegaToP : Omega →ₐ[F] P,
      Function.Injective omegaToP ∧
        (∀ x : F,
          omegaToP (genericTensorFieldComponentLeft mF x) =
            algebraMap F P x) ∧
        (∀ x : M,
          omegaToP (genericTensorFieldComponentRight mF x) =
            fPrefix x) := by
  classical
  dsimp only
  let fF : F →ₐ[K] P := IsScalarTower.toAlgHom K F P
  let Eimage : IntermediateField K P := fPrefix.fieldRange
  let Fimage : IntermediateField K P := fF.fieldRange
  let : FiniteDimensional K Eimage :=
    fPrefix.toLinearMap.finiteDimensional_range
  let eGeneric : (K ⊗[K] M) ≃ₐ[K] Eimage :=
    (Algebra.TensorProduct.lid K M).trans fPrefix.equivFieldRange
  let mActual := actualCompositumGenericComponentIdeal
    (A := K) (T := M) (F := K) (Omega := P)
    Eimage Fimage eGeneric
  let : mActual.IsMaximal :=
    actualCompositumGenericComponentIdeal_isMaximal
      Eimage Fimage eGeneric
  let eF : F ≃ₐ[K] Fimage := fF.equivFieldRange
  let eTensorF : (F ⊗[K] M) ≃ₐ[K] (Fimage ⊗[K] M) :=
    Algebra.TensorProduct.congr eF (AlgEquiv.refl : M ≃ₐ[K] M)
  let mF := mActual.comap eTensorF.toRingEquiv.toRingHom
  let : mF.IsMaximal :=
    (inferInstance : mActual.IsMaximal).comap_bijective
      eTensorF.toRingEquiv.toRingHom eTensorF.bijective
  let Omega := GenericTensorFieldComponent mF
  have hmMap :
      mActual = mF.map eTensorF.toRingEquiv.toRingHom := by
    exact (Ideal.map_comap_of_surjective
      eTensorF.toRingEquiv.toRingHom eTensorF.surjective mActual).symm
  let eComponent : Omega ≃ₐ[K]
      GenericTensorFieldComponent mActual :=
    Ideal.quotientEquivAlg mF mActual eTensorF hmMap
  let eActualK : GenericTensorFieldComponent mActual ≃ₐ[K]
      (Eimage ⊔ Fimage : IntermediateField K P) :=
    (actualCompositumGenericComponentAlgEquiv
      Eimage Fimage eGeneric).restrictScalars K
  let eAmbientK : Omega ≃ₐ[K]
      (Eimage ⊔ Fimage : IntermediateField K P) :=
    eComponent.trans eActualK
  let ambientInclusion :
      (Eimage ⊔ Fimage : IntermediateField K P) →ₐ[K] P :=
    (Eimage ⊔ Fimage : IntermediateField K P).val
  let omegaToPK : Omega →ₐ[K] P :=
    ambientInclusion.comp eAmbientK.toAlgHom
  let omegaToP : Omega →ₐ[F] P :=
    { omegaToPK.toRingHom with
      commutes' := by
        intro x
        change
          omegaToPK (genericTensorFieldComponentLeft mF x) =
            algebraMap F P x
        change
          (((actualCompositumGenericComponentAlgEquiv
                Eimage Fimage eGeneric)
              (Ideal.quotientEquivAlg mF mActual eTensorF hmMap
                (genericTensorFieldComponentLeft mF x)) :
                  (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
            algebraMap F P x
        rw [genericTensorFieldComponentLeft_apply,
          Ideal.quotientEquivAlg_mk mActual eTensorF hmMap,
          actualCompositumGenericComponentAlgEquiv_mk]
        change
          (((actualCompositumGenericComponentMap
                Eimage Fimage eGeneric)
              (eTensorF
                ((Algebra.TensorProduct.includeLeft :
                  F →ₐ[K] F ⊗[K] M) x)) :
                (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
            algebraMap F P x
        rw [show eTensorF
            ((Algebra.TensorProduct.includeLeft :
              F →ₐ[K] F ⊗[K] M) x) =
              (Algebra.TensorProduct.includeLeft :
                Fimage →ₐ[K] Fimage ⊗[K] M) (eF x) by
          change eTensorF (x ⊗ₜ[K] (1 : M)) =
            eF x ⊗ₜ[K] (1 : M)
          simp [eTensorF]]
        change
          (((actualCompositumGenericComponentMap
                Eimage Fimage eGeneric)
              ((eF x) ⊗ₜ[K] (1 : M)) :
                (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
            algebraMap F P x
        rw [actualCompositumGenericComponentMap_tmul_left_coe]
        rfl }
  have hLeftCoordinate (x : F) :
      omegaToP (genericTensorFieldComponentLeft mF x) =
        algebraMap F P x :=
    omegaToP.commutes x
  have hRightCoordinate (x : M) :
      omegaToP (genericTensorFieldComponentRight mF x) =
        fPrefix x := by
    change
      (((actualCompositumGenericComponentAlgEquiv
            Eimage Fimage eGeneric)
          (Ideal.quotientEquivAlg mF mActual eTensorF hmMap
            (genericTensorFieldComponentRight mF x)) :
              (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
        fPrefix x
    rw [genericTensorFieldComponentRight_apply,
      Ideal.quotientEquivAlg_mk mActual eTensorF hmMap,
      actualCompositumGenericComponentAlgEquiv_mk]
    change
      (((actualCompositumGenericComponentMap Eimage Fimage eGeneric)
          (eTensorF
            ((Algebra.TensorProduct.includeRight :
              M →ₐ[K] F ⊗[K] M) x)) :
            (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
        fPrefix x
    rw [show eTensorF
        ((Algebra.TensorProduct.includeRight :
          M →ₐ[K] F ⊗[K] M) x) =
          (Algebra.TensorProduct.includeRight :
            M →ₐ[K] Fimage ⊗[K] M) x by
      change eTensorF ((1 : F) ⊗ₜ[K] x) =
        (1 : Fimage) ⊗ₜ[K] x
      simp [eTensorF]]
    change
      (((actualCompositumGenericComponentMap Eimage Fimage eGeneric)
          ((1 : Fimage) ⊗ₜ[K] x) :
            (Eimage ⊔ Fimage : IntermediateField K P)) : P) =
        fPrefix x
    rw [actualCompositumGenericComponentMap_tmul_right_coe]
    simpa only [eGeneric, AlgEquiv.trans_apply, Algebra.TensorProduct.lid_tmul, one_smul]
      using AlgHom.equivFieldRange_apply_coe (f := fPrefix) x
  exact ⟨omegaToP, omegaToP.injective,
    hLeftCoordinate, hRightCoordinate⟩

end EtaleFundamentalGroups.Kummer

end
