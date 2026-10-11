/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CechLocalizationComplex
import EtaleFundamentalGroups.Purity.TensorComplexCoefficientFunctor
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The canonical degree-zero term of the Čech complex

The antidiagonal indexing the zeroth term has exactly one summand.
Its inclusion identifies the zeroth term of each Čech factor with the
ring. Tensoring this identification gives the canonical coefficient
identification, natural in every module.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

private def tensorZeroSummandOut (K L : CochainComplex (ModuleCat.{u} R) ℕ)
    (i j : ℕ) (hij : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) (i, j) = 0) :
    ((curriedTensor (ModuleCat.{u} R)).obj (K.X i)).obj (L.X j) ⟶ K.X 0 ⊗ L.X 0 := by
  have h : i + j = 0 := hij
  have hi : i = 0 := by omega
  have hj : j = 0 := by omega
  exact (K.XIsoOfEq hi).hom ⊗ₘ (L.XIsoOfEq hj).hom

/-- In degree zero a nonnegative tensor complex has its unique
`(0,0)` summand. -/
def tensorComplexZeroIso (K L : CochainComplex (ModuleCat.{u} R) ℕ) :
    K.X 0 ⊗ L.X 0 ≅ (HomologicalComplex.tensorObj K L).X 0 where
  hom := ιTensorObj K L 0 0 0 rfl
  inv := mapBifunctorDesc (F := curriedTensor (ModuleCat.{u} R))
    (c := ComplexShape.up ℕ) (tensorZeroSummandOut K L)
  hom_inv_id := by
    rw [ι_mapBifunctorDesc]
    change (𝟙 (K.X 0) ⊗ₘ 𝟙 (L.X 0)) = 𝟙 _
    exact id_tensorHom_id (K.X 0) (L.X 0)
  inv_hom_id := by
    apply mapBifunctor.hom_ext
    intro i j hij
    have h : i + j = 0 := hij
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    rw [← Category.assoc, ι_mapBifunctorDesc]
    change (𝟙 (K.X 0) ⊗ₘ 𝟙 (L.X 0)) ≫ ιTensorObj K L 0 0 0 rfl =
      ιTensorObj K L 0 0 0 rfl ≫ 𝟙 _
    rw [id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- The zeroth Čech term is canonically the coefficient ring. -/
def cechLocalizationZeroIso : (xs : List R) →
    (cechLocalizationComplex xs).X 0 ≅ ModuleCat.of R R
  | [] => singleObjXSelf (ComplexShape.up ℕ) 0 (ModuleCat.of R R)
  | x :: xs =>
    (tensorComplexZeroIso (principalLocalizationComplex x (ModuleCat.of R R))
      (cechLocalizationComplex xs)).symm ≪≫
      (tensorLeft (ModuleCat.of R R)).mapIso (cechLocalizationZeroIso xs) ≪≫
      λ_ (ModuleCat.of R R)

/-- The canonical degree-zero coefficient identification. -/
def cechCoefficientZeroIso (xs : List R) (M : ModuleCat.{u} R) :
    (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cechLocalizationComplex xs)).X 0 ≅ M :=
  (tensorLeft M).mapIso (cechLocalizationZeroIso xs) ≪≫ ρ_ M

/-- Degree-zero coefficient identification commutes with every
coefficient morphism. -/
theorem cechCoefficientZeroIso_naturality (xs : List R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map f).f 0 ≫
      (cechCoefficientZeroIso xs N).hom = (cechCoefficientZeroIso xs M).hom ≫ f := by
  change (f ▷ (cechLocalizationComplex xs).X 0) ≫
    (N ◁ (cechLocalizationZeroIso xs).hom) ≫ (ρ_ N).hom =
      ((M ◁ (cechLocalizationZeroIso xs).hom) ≫ (ρ_ M).hom) ≫ f
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change (M ◁ (cechLocalizationZeroIso xs).hom) ≫
    (f ▷ (𝟙_ (ModuleCat.{u} R))) ≫ (ρ_ N).hom =
      ((M ◁ (cechLocalizationZeroIso xs).hom) ≫ (ρ_ M).hom) ≫ f
  rw [rightUnitor_naturality]
  exact (Category.assoc _ _ _).symm

/-- Degree-zero Čech cohomology, embedded in the coefficient module. -/
def cechHomologyZeroToModule (xs : List R) (M : ModuleCat.{u} R) :
    ((((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cechLocalizationComplex xs)).homology 0) ⟶ M :=
  let K := ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cechLocalizationComplex xs)
  (CochainComplex.isoHomologyπ₀ K).inv ≫ K.iCycles 0 ≫ (cechCoefficientZeroIso xs M).hom

/-- The zeroth cohomology embeds because a nonnegative cochain complex
has no incoming boundaries in degree zero. -/
instance cechHomologyZeroToModule_mono (xs : List R) (M : ModuleCat.{u} R) :
    Mono (cechHomologyZeroToModule xs M) := by
  dsimp only [cechHomologyZeroToModule]
  infer_instance

/-- The embedding of degree-zero cohomology is natural in coefficients. -/
theorem cechHomologyZeroToModule_naturality (xs : List R)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    homologyMap ((tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map f) 0 ≫
      cechHomologyZeroToModule xs N = cechHomologyZeroToModule xs M ≫ f := by
  let K : CochainComplex (ModuleCat.{u} R) ℕ :=
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cechLocalizationComplex xs)
  let L : CochainComplex (ModuleCat.{u} R) ℕ :=
    ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cechLocalizationComplex xs)
  let φ : K ⟶ L := (tensorComplexCoefficientFunctor (cechLocalizationComplex xs)).map f
  have hzero : φ.f 0 ≫ (cechCoefficientZeroIso xs N).hom =
      (cechCoefficientZeroIso xs M).hom ≫ f := cechCoefficientZeroIso_naturality xs f
  change homologyMap φ 0 ≫ (CochainComplex.isoHomologyπ₀ L).inv ≫
      L.iCycles 0 ≫ (cechCoefficientZeroIso xs N).hom =
    ((CochainComplex.isoHomologyπ₀ K).inv ≫ K.iCycles 0 ≫
      (cechCoefficientZeroIso xs M).hom) ≫ f
  rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc, cyclesMap_i_assoc, hzero]
  simp only [Category.assoc]


end EtaleFundamentalGroups.Purity

end
