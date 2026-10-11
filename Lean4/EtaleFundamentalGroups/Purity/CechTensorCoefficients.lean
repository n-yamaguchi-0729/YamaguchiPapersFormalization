/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison

The single-factor differential calculation is adapted from Mathlib's
`Algebra/Homology/Monoidal.lean` at revision
065356127b1dc0016f66b7283ce0ce2c4055aa55:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Homology/Monoidal.lean
The general coefficient comparison is by Naganori Yamaguchi
(assisted by OpenAI Codex).
-/

import EtaleFundamentalGroups.Purity.CechLocalizationComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Monoidal

/-!
# Tensor coefficients in the bounded Čech complex

The tensor complex with a coefficient module concentrated in degree zero
is naturally identified degreewise with tensoring each original term by
that coefficient module. The construction uses the unique nonzero
summand in each degree, and verifies compatibility with the differential.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

private abbrev coefficientSingle (M : ModuleCat.{u} R) :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℕ) 0).obj M

private def singleTensorInto (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    M ⊗ K.X n ⟶ (HomologicalComplex.tensorObj (coefficientSingle M) K).X n :=
  ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X n) ≫
    ιTensorObj (coefficientSingle M) K 0 n n (zero_add n)

private def singleTensorSummandOut (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n i j : ℕ)
    (hij : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (i, j) = n) :
    ((curriedTensor (ModuleCat.{u} R)).obj (coefficientSingle M |>.X i)).obj
      (K.X j) ⟶ M ⊗ K.X n :=
  if hi : i = 0 then
    ((singleObjXIsoOfEq (ComplexShape.up ℕ) 0 M i hi).hom ▷ K.X j) ≫
      (M ◁ (K.XIsoOfEq (by have h : i + j = n := hij; omega : j = n)).hom)
  else 0

private def singleTensorOut (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (coefficientSingle M) K).X n ⟶ M ⊗ K.X n :=
  mapBifunctorDesc (F := curriedTensor (ModuleCat.{u} R))
    (c := ComplexShape.up ℕ) (singleTensorSummandOut M K n)

private theorem singleTensorInto_out (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    singleTensorInto M K n ≫ singleTensorOut M K n = 𝟙 _ := by
  dsimp only [singleTensorInto, singleTensorOut]
  rw [Category.assoc, ι_mapBifunctorDesc]
  dsimp only [singleTensorSummandOut]
  rw [dite_eq_left rfl]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom,
    MonoidalCategory.whiskerLeft_id, Category.comp_id,
    ← MonoidalCategory.comp_whiskerRight]
  change ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ≫
    (singleObjXSelf (ComplexShape.up ℕ) 0 M).hom) ▷ K.X n = 𝟙 _
  rw [Iso.inv_hom_id, id_whiskerRight]

private theorem singleTensorOut_into (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    singleTensorOut M K n ≫ singleTensorInto M K n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro i j hij
  have hij' : i + j = n := hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by omega
    subst j
    dsimp only [singleTensorOut]
    rw [← Category.assoc, ι_mapBifunctorDesc]
    dsimp only [singleTensorSummandOut, singleTensorInto]
    rw [dite_eq_left rfl]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom,
      MonoidalCategory.whiskerLeft_id, Category.comp_id]
    change ((singleObjXSelf (ComplexShape.up ℕ) 0 M).hom ▷ K.X n) ≫
      ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X n) ≫
        ιTensorObj (coefficientSingle M) K 0 n n (zero_add n) =
      ιTensorObj (coefficientSingle M) K 0 n n (zero_add n)
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]
  · exact ((tensorRight (K.X j)).map_isZero
      (isZero_single_obj_X (ComplexShape.up ℕ) 0 M i hi)).eq_of_src _ _

private def singleTensorXIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    M ⊗ K.X n ≅ (HomologicalComplex.tensorObj (coefficientSingle M) K).X n where
  hom := singleTensorInto M K n
  inv := singleTensorOut M K n
  hom_inv_id := singleTensorInto_out M K n
  inv_hom_id := singleTensorOut_into M K n

private theorem single_tensor_d₁ (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (i j n : ℕ) :
    mapBifunctor.d₁ (coefficientSingle M) K (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℕ) i j n = 0 := by
  by_cases hi : (ComplexShape.up ℕ).Rel i ((ComplexShape.up ℕ).next i)
  · by_cases hn : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ) ((ComplexShape.up ℕ).next i, j) = n
    · rw [mapBifunctor.d₁_eq _ _ _ _ hi _ _ hn, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ hi _ _ hn]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hi]

private theorem singleTensorInto_comm (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ) :
    singleTensorInto M K i ≫ (HomologicalComplex.tensorObj (coefficientSingle M) K).d i j =
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ) |>.obj K).d i j ≫
        singleTensorInto M K j := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · simp only [singleTensorInto, Category.assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      single_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (zero_add j)]
    change ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X i) ≫
      ((1 : ℤ) • (((coefficientSingle M).X 0 ◁ K.d i j) ≫
        ιTensorObj (coefficientSingle M) K 0 j j (zero_add j))) =
      (M ◁ K.d i j) ≫ ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X j) ≫
        ιTensorObj (coefficientSingle M) K 0 j j (zero_add j)
    rw [one_smul, ← whisker_exchange_assoc]
  · rw [HomologicalComplex.shape _ _ _ hij, comp_zero,
      HomologicalComplex.shape _ _ _ hij, zero_comp]

/-- Tensoring a complex with a module concentrated in degree zero is the
same complex as tensoring every term with that module. -/
def singleTensorComplexIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj K ≅
      HomologicalComplex.tensorObj ((HomologicalComplex.single (ModuleCat.{u} R)
        (ComplexShape.up ℕ) 0).obj M) K :=
  HomologicalComplex.Hom.isoOfComponents (singleTensorXIso M K)
    (fun i j _ => singleTensorInto_comm M K i j)

/-- The coefficient comparison includes the unique single-factor
summand in each degree. -/
theorem singleTensorComplexIso_hom_f (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (singleTensorComplexIso M K).hom.f n =
      ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X n) ≫
        ιTensorObj ((HomologicalComplex.single (ModuleCat.{u} R)
          (ComplexShape.up ℕ) 0).obj M) K 0 n n (zero_add n) := rfl

end EtaleFundamentalGroups.Purity
