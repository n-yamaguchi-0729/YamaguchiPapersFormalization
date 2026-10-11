/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CechInjectiveHomotopy
import Nyll.EtaleFundamentalGroups.Purity.CechLocalizationDegreeZero
import Nyll.EtaleFundamentalGroups.Purity.CechTensorCoefficients
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationTensorCoefficients
import Nyll.EtaleFundamentalGroups.Purity.CechLocalizationComplex
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionInjective
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionSum
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationHomotopy
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Homology.BifunctorAssociator
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Degree-zero maps in the injective Čech contraction

The degree-zero map of the injective Čech contraction is identified with the
canonical torsion inclusion using the tensor coefficient comparisons.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- The coefficient comparison inserts the unique zero-degree summand. -/
theorem singleTensorComplexIso_hom_f_zero (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    (singleTensorComplexIso M K).hom.f 0 =
      (tensorComplexZeroIso ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M) K).hom := by
  calc
    _ = ((singleObjXSelf (ComplexShape.up ℕ) 0 M).inv ▷ K.X 0) ≫
        ιTensorObj ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M) K 0 0 0 rfl :=
      singleTensorComplexIso_hom_f M K 0
    _ = _ := by
      change (𝟙 M ▷ K.X 0) ≫
        ιTensorObj ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M) K 0 0 0 rfl = _
      rw [id_whiskerRight]
      exact Category.id_comp _

/-- The inverse coefficient comparison projects the unique zero-degree summand. -/
theorem singleTensorComplexIso_inv_f_zero (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℕ) :
    (singleTensorComplexIso M K).inv.f 0 =
      (tensorComplexZeroIso ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M) K).inv := by
  have h : ((HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) 0).mapIso
      (singleTensorComplexIso M K)) =
      tensorComplexZeroIso ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M) K :=
    Iso.ext (singleTensorComplexIso_hom_f_zero M K)
  exact congrArg Iso.inv h

/-- The principal coefficient comparison is the right unitor in degree zero. -/
theorem principalLocalizationTensorCoefficientsIso_inv_f_zero
    (x : R) (M : ModuleCat.{u} R) :
    (principalLocalizationTensorCoefficientsIso x M).inv.f 0 = (ρ_ M).inv := rfl

/-- Tensor maps act on the unique degree-zero summand by their two
zeroth components. -/
theorem tensorComplexZeroIso_hom_naturality
    {K L K' L' : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    (tensorComplexZeroIso K L).hom ≫ (HomologicalComplex.tensorHom f g).f 0 =
      (f.f 0 ⊗ₘ g.f 0) ≫ (tensorComplexZeroIso K' L').hom := by
  have h : (tensorComplexZeroIso K L).hom ≫
      (HomologicalComplex.tensorHom f g).f 0 =
      (f.f 0 ▷ L.X 0) ≫ (K'.X 0 ◁ g.f 0) ≫ (tensorComplexZeroIso K' L').hom :=
    ι_mapBifunctorMap f g (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℕ) 0 0 0 rfl
  refine h.trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg
    (fun k : K.X 0 ⊗ L.X 0 ⟶ K'.X 0 ⊗ L'.X 0 =>
      k ≫ (tensorComplexZeroIso K' L').hom) (tensorHom_def (f.f 0) (g.f 0)).symm

/-- The inverse degree-zero identification also commutes with tensor maps. -/
theorem tensorComplexZeroIso_inv_naturality
    {K L K' L' : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    (HomologicalComplex.tensorHom f g).f 0 ≫ (tensorComplexZeroIso K' L').inv =
      (tensorComplexZeroIso K L).inv ≫ (f.f 0 ⊗ₘ g.f 0) := by
  apply (cancel_epi (tensorComplexZeroIso K L).hom).mp
  rw [← Category.assoc, tensorComplexZeroIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The associator on complexes is the usual tensor associator on the
unique summands in degree zero. -/
theorem tensorComplexZeroIso_associator_hom
    (K L B : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorComplexZeroIso K L).hom ▷ B.X 0) ≫
      (tensorComplexZeroIso (HomologicalComplex.tensorObj K L) B).hom ≫
      (HomologicalComplex.associator K L B).hom.f 0 =
    (α_ (K.X 0) (L.X 0) (B.X 0)).hom ≫
      (K.X 0 ◁ (tensorComplexZeroIso L B).hom) ≫
      (tensorComplexZeroIso K (HomologicalComplex.tensorObj L B)).hom := by
  have h := ι_mapBifunctorAssociatorX_hom
    (curriedAssociatorNatIso (ModuleCat.{u} R)) K L B
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) 0 0 0 0 rfl
  rw [mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ 0 0 0 0 0 rfl rfl,
    mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ 0 0 0 0 0 rfl rfl] at h
  have h' : (((tensorComplexZeroIso K L).hom ▷ B.X 0) ≫
      (tensorComplexZeroIso (HomologicalComplex.tensorObj K L) B).hom) ≫
      (HomologicalComplex.associator K L B).hom.f 0 =
    (α_ (K.X 0) (L.X 0) (B.X 0)).hom ≫
      (K.X 0 ◁ (tensorComplexZeroIso L B).hom) ≫
      (tensorComplexZeroIso K (HomologicalComplex.tensorObj L B)).hom := h
  exact (Category.assoc _ _ _).symm.trans h'

private theorem tensorComplexZeroIso_associator_hom_normalized
    (K L B : CochainComplex (ModuleCat.{u} R) ℕ) :
    (tensorComplexZeroIso (HomologicalComplex.tensorObj K L) B).hom ≫
      (HomologicalComplex.associator K L B).hom.f 0 ≫
      (tensorComplexZeroIso K (HomologicalComplex.tensorObj L B)).inv =
    ((tensorComplexZeroIso K L).inv ▷ B.X 0) ≫
      (α_ (K.X 0) (L.X 0) (B.X 0)).hom ≫
      (K.X 0 ◁ (tensorComplexZeroIso L B).hom) := by
  apply (cancel_epi ((tensorComplexZeroIso K L).hom ▷ B.X 0)).mp
  have h := congrArg
    (fun k => k ≫ (tensorComplexZeroIso K (HomologicalComplex.tensorObj L B)).inv)
    (tensorComplexZeroIso_associator_hom K L B)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  rw [h, ← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight, Category.id_comp]

private theorem tensorComplexZeroIso_tensor_associator
    (K K' L B : CochainComplex (ModuleCat.{u} R) ℕ)
    (f : K ⟶ HomologicalComplex.tensorObj K' L) :
    (tensorComplexZeroIso K B).hom ≫
      (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
      (HomologicalComplex.associator K' L B).hom.f 0 ≫
      (tensorComplexZeroIso K' (HomologicalComplex.tensorObj L B)).inv =
    (f.f 0 ▷ B.X 0) ≫ ((tensorComplexZeroIso K' L).inv ▷ B.X 0) ≫
      (α_ (K'.X 0) (L.X 0) (B.X 0)).hom ≫
      (K'.X 0 ◁ (tensorComplexZeroIso L B).hom) := by
  rw [← Category.assoc, ← Category.assoc, tensorComplexZeroIso_hom_naturality]
  rw [HomologicalComplex.id_f, tensorHom_id, Category.assoc, Category.assoc,
    tensorComplexZeroIso_associator_hom_normalized]

private theorem zeroTensorModuleCompatibility
    (M T B Y Z : ModuleCat.{u} R) (i : T ⟶ M) (f : T ⟶ Y)
    (u : M ⊗ ModuleCat.of R R ≅ Y) (v : ModuleCat.of R R ⊗ B ≅ Z)
    (b : B ⟶ ModuleCat.of R R) (hf : f = i ≫ (ρ_ M).inv ≫ u.hom) :
    ((f ▷ B) ≫ (u.inv ▷ B) ≫ (α_ M (ModuleCat.of R R) B).hom ≫ (M ◁ v.hom)) ≫
      ((M ◁ (v.inv ≫ (ModuleCat.of R R ◁ b) ≫ (λ_ (ModuleCat.of R R)).hom)) ≫
        (ρ_ M).hom) = ((T ◁ b) ≫ (ρ_ T).hom) ≫ i := by
  have hh : f ≫ u.inv = i ≫ (ρ_ M).inv := by
    rw [hf]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← comp_whiskerRight_assoc, hh]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc]
  have hu : ((ρ_ M).inv ▷ B) ≫ (α_ M (ModuleCat.of R R) B).hom ≫
      (M ◁ ((ModuleCat.of R R ◁ b) ≫ (λ_ (ModuleCat.of R R)).hom)) ≫
      (ρ_ M).hom = (M ◁ b) ≫ (ρ_ M).hom := by
    rw [whiskerLeft_comp]
    monoidal
  rw [comp_whiskerRight, Category.assoc, hu]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change (T ◁ b) ≫ (i ▷ (𝟙_ (ModuleCat.{u} R))) ≫ (ρ_ M).hom =
    ((T ◁ b) ≫ (ρ_ T).hom) ≫ i
  rw [rightUnitor_naturality]
  exact (Category.assoc _ _ _).symm

private theorem cechPrincipalTensor_zero (x : R) (xs : List R) (M T : ModuleCat.{u} R) (i : T ⟶ M)
    (f : (CochainComplex.single₀ (ModuleCat.{u} R)).obj T ⟶
      HomologicalComplex.tensorObj ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M)
        (principalLocalizationComplex x (ModuleCat.of R R)))
    (hf : f.f 0 = i ≫ (ρ_ M).inv ≫
      (tensorComplexZeroIso ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M)
        (principalLocalizationComplex x (ModuleCat.of R R))).hom) :
    (singleTensorComplexIso T (cechLocalizationComplex xs)).hom.f 0 ≫
      (HomologicalComplex.tensorHom f (𝟙 (cechLocalizationComplex xs))).f 0 ≫
      (HomologicalComplex.associator
        ((CochainComplex.single₀ (ModuleCat.{u} R)).obj M)
        (principalLocalizationComplex x (ModuleCat.of R R))
        (cechLocalizationComplex xs)).hom.f 0 ≫
      (singleTensorComplexIso M (cechLocalizationComplex (x :: xs))).inv.f 0 ≫
      (cechCoefficientZeroIso (x :: xs) M).hom =
    (cechCoefficientZeroIso xs T).hom ≫ i := by
  let A := principalLocalizationComplex x (ModuleCat.of R R)
  let B := cechLocalizationComplex xs
  let S := (CochainComplex.single₀ (ModuleCat.{u} R)).obj M
  let U := (CochainComplex.single₀ (ModuleCat.{u} R)).obj T
  let u : M ⊗ ModuleCat.of R R ≅ (HomologicalComplex.tensorObj S A).X 0 :=
    tensorComplexZeroIso S A
  let v : ModuleCat.of R R ⊗ B.X 0 ≅ (HomologicalComplex.tensorObj A B).X 0 :=
    tensorComplexZeroIso A B
  let j : T ⟶ (HomologicalComplex.tensorObj S A).X 0 := f.f 0
  let a : T ⊗ B.X 0 ⟶ (HomologicalComplex.tensorObj U B).X 0 :=
    (singleTensorComplexIso T B).hom.f 0
  let k : (HomologicalComplex.tensorObj S (HomologicalComplex.tensorObj A B)).X 0 ⟶
      M ⊗ (HomologicalComplex.tensorObj A B).X 0 :=
    (singleTensorComplexIso M (HomologicalComplex.tensorObj A B)).inv.f 0
  have hs : a = (tensorComplexZeroIso U B).hom :=
    singleTensorComplexIso_hom_f_zero T B
  have ht : k = (tensorComplexZeroIso S (HomologicalComplex.tensorObj A B)).inv :=
    singleTensorComplexIso_inv_f_zero M (HomologicalComplex.tensorObj A B)
  have h := tensorComplexZeroIso_tensor_associator U S A B f
  have h' : a ≫ (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
      (HomologicalComplex.associator S A B).hom.f 0 ≫ k =
      (j ▷ B.X 0) ≫ (u.inv ▷ B.X 0) ≫
      (α_ M (ModuleCat.of R R) (B.X 0)).hom ≫ (M ◁ v.hom) := by
    calc
      _ = (tensorComplexZeroIso U B).hom ≫
          (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
          (HomologicalComplex.associator S A B).hom.f 0 ≫
          (tensorComplexZeroIso S (HomologicalComplex.tensorObj A B)).inv := by
        exact congrArg₂ (fun a' k' => a' ≫ (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
          (HomologicalComplex.associator S A B).hom.f 0 ≫ k') hs ht
      _ = _ := h
  let c : M ⊗ (HomologicalComplex.tensorObj A B).X 0 ⟶ M :=
    (cechCoefficientZeroIso (x :: xs) M).hom
  have h'' := congrArg (fun l => l ≫ c) h'
  have hnorm : ((j ▷ B.X 0) ≫ (u.inv ▷ B.X 0) ≫
      (α_ M (ModuleCat.of R R) (B.X 0)).hom ≫ (M ◁ v.hom)) ≫ c =
      (cechCoefficientZeroIso xs T).hom ≫ i :=
    zeroTensorModuleCompatibility M T (B.X 0) _ _ i j u v
      (cechLocalizationZeroIso xs).hom hf
  have hout := h''.trans hnorm
  have he : a ≫ (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
      (HomologicalComplex.associator S A B).hom.f 0 ≫ k ≫ c =
      (cechCoefficientZeroIso xs T).hom ≫ i := by
    simpa only [Category.assoc] using hout
  exact he

/-- The injection in the Čech contraction is the canonical torsion inclusion
under the degree-zero coefficient identification. -/
theorem cechInjectiveHomotopyEquiv_inv_f_zero [IsNoetherianRing R]
    (xs : List R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    (cechInjectiveHomotopyEquiv xs M).inv.f 0 ≫
      (cechCoefficientZeroIso xs M).hom =
    ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList xs)).subtype := by
  induction xs generalizing M with
  | nil =>
      let T := ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList ([] : List R)))
      let i : T ⟶ M :=
        ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList ([] : List R))).subtype
      let f : T ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R) := (cechInjectiveHomotopyEquiv [] M).inv.f 0
      let c : M ⊗ 𝟙_ (ModuleCat.{u} R) ⟶ M := (cechCoefficientZeroIso [] M).hom
      have hf : f = i ≫ (ρ_ M).inv := by
        have h : f = (cechNilTorsionIso M).inv ≫ (ρ_ M).inv :=
          cechNilHomotopyEquiv_inv_f_zero M T (cechNilTorsionIso M)
        exact h.trans (congrArg (fun k : T ⟶ M => k ≫ (ρ_ M).inv)
          (cechNilTorsionIso_inv M))
      have hc : c = (ρ_ M).hom := by
        change (M ◁ 𝟙 (𝟙_ (ModuleCat.{u} R))) ≫ (ρ_ M).hom = _
        rw [whiskerLeft_id, Category.id_comp]
      change f ≫ c = i
      rw [hf, hc]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | cons x xs ih =>
      let A := principalLocalizationComplex x (ModuleCat.of R R)
      let B := cechLocalizationComplex xs
      let S := (CochainComplex.single₀ (ModuleCat.{u} R)).obj M
      let T := ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))
      let U := (CochainComplex.single₀ (ModuleCat.{u} R)).obj T
      let : Module.Injective R T := moduleInjective_primaryComponent (Ideal.span {x}) M
      let i : T ⟶ M := ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.span {x})).subtype
      let q : Ideal.primaryComponent T (Ideal.ofList xs) ≃ₗ[R]
          Ideal.primaryComponent M (Ideal.ofList (x :: xs)) :=
        (primaryComponentIteratedLinearEquiv M (Ideal.span {x}) (Ideal.ofList xs)).trans
          (LinearEquiv.ofEq _ _ (congrArg
            (fun I : Ideal R => Ideal.primaryComponent M I) (Ideal.ofList_cons x xs).symm))
      let f : U ⟶ HomologicalComplex.tensorObj S A :=
        (principalLocalizationHomotopyEquiv x M).hom ≫
          (principalLocalizationTensorCoefficientsIso x M).inv ≫ (singleTensorComplexIso M A).hom
      have hf : f.f 0 = i ≫ (ρ_ M).inv ≫ (tensorComplexZeroIso S A).hom := by
        exact congrArg₂ (fun (a : T ⟶ M)
          (b : M ⊗ ModuleCat.of R R ⟶ (HomologicalComplex.tensorObj S A).X 0) =>
            a ≫ (ρ_ M).inv ≫ b)
          (principalLocalizationHomotopyEquiv_hom_f_zero x M)
          (singleTensorComplexIso_hom_f_zero M A)
      let W := ModuleCat.of R (Ideal.primaryComponent T (Ideal.ofList xs))
      let Q := ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList (x :: xs)))
      let r : W ⟶ T ⊗ B.X 0 := (cechInjectiveHomotopyEquiv xs T).inv.f 0
      let c : T ⊗ B.X 0 ⟶ T := (cechCoefficientZeroIso xs T).hom
      let j : W ⟶ T := ModuleCat.ofHom (Ideal.primaryComponent T (Ideal.ofList xs)).subtype
      let k : Q ⟶ W := q.toModuleIso.inv
      let s : Q ⟶ M := ModuleCat.ofHom
        (Ideal.primaryComponent M (Ideal.ofList (x :: xs))).subtype
      let l : T ⊗ B.X 0 ⟶ M :=
        (singleTensorComplexIso T B).hom.f 0 ≫
          (HomologicalComplex.tensorHom f (𝟙 B)).f 0 ≫
          (HomologicalComplex.associator S A B).hom.f 0 ≫
          (singleTensorComplexIso M (cechLocalizationComplex (x :: xs))).inv.f 0 ≫
          (cechCoefficientZeroIso (x :: xs) M).hom
      have hl : l = c ≫ i := cechPrincipalTensor_zero x xs M T i f hf
      have hr : r ≫ c = j := ih T
      have hq : k ≫ j ≫ i = s := by
        have hval (w : Ideal.primaryComponent T (Ideal.ofList xs)) :
            (q w : M) = ((w : T) : M) := by
          dsimp only [q, LinearEquiv.trans_apply]
          rw [LinearEquiv.coe_ofEq_apply]
          exact primaryComponentIteratedLinearEquiv_apply_val M (Ideal.span {x}) (Ideal.ofList xs) w
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (((q.symm z : Ideal.primaryComponent T (Ideal.ofList xs)) : T) : M) = (z : M)
        exact (hval (q.symm z)).symm.trans
          (congrArg (fun w : Ideal.primaryComponent M (Ideal.ofList (x :: xs)) => (w : M))
            (q.apply_symm_apply z))
      have hout : k ≫ r ≫ l = s := by
        rw [hl, ← Category.assoc r c i, hr, hq]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      let w : Q := z
      change l (r (k w)) = s w
      exact ConcreteCategory.congr_hom hout w

end EtaleFundamentalGroups.Purity

end
