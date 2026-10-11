/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponent
import EtaleFundamentalGroups.GaloisCovers.FunctionFieldResidueNaturality
import EtaleFundamentalGroups.GaloisCovers.FiniteEtaleGenericResidue
import EtaleFundamentalGroups.GaloisCovers.PullbackComponentGenericResidueArtinian
import EtaleFundamentalGroups.GaloisCovers.PullbackFunctionFieldTensorSurjectivity
import SchemeTheory.FiniteEtale.BaseChange.PullbackResidueArtinian
import SchemeTheory.FiniteEtale.BaseChange.PullbackResidueTensorProduct
import EtaleFundamentalGroups.FiniteEtale.FunctionField
import EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField

/-!
# Function fields of connected pullback components

This file ties an actual connected component of a pulled-back finite-etale
cover to the corresponding component of the tensor product of function
fields.  In particular, the comparison is selected by the given component
map; it is not an abstract choice of an isomorphic field.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}}

private theorem eqToHom_stalk_eq_stalkCongr
    (T : Scheme.{u}) {x x' : T} (h : x = x') :
    eqToHom (congrArg (fun q ↦ T.presheaf.stalk q) h) =
      (T.presheaf.stalkCongr (.of_eq h)).hom := by
  subst x'
  simp

/-- Function-field maps do not depend on the presentation of an equal dense
morphism (nor on the proof of density). -/
private theorem functionFieldMap_eq_of_eq
    {T S : Scheme.{u}} [IsIntegral T] [IsIntegral S]
    (a b : S ⟶ T) (hab : a = b)
    (ha : DenseRange a) (hb : DenseRange b) :
    a.functionFieldMap ha = b.functionFieldMap hb := by
  subst b
  rfl

/-- Function-field maps are functorial for composable dense morphisms. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.functionFieldMap_comp_of_denseRange
    {T S R : Scheme.{u}} [IsIntegral T] [IsIntegral S] [IsIntegral R]
    (f : S ⟶ T) (hf : DenseRange f)
    (g : R ⟶ S) (hg : DenseRange g) :
    let hgf : DenseRange (g ≫ f) := by
      change DenseRange (f.base ∘ g.base)
      exact hf.comp hg f.continuous
    (g.functionFieldMap hg).comp (f.functionFieldMap hf) =
      (g ≫ f).functionFieldMap hgf := by
  let hgf : DenseRange (g ≫ f) := by
    change DenseRange (f.base ∘ g.base)
    exact hf.comp hg f.continuous
  change (g.functionFieldMap hg).comp (f.functionFieldMap hf) =
    (g ≫ f).functionFieldMap hgf
  let hfgeneric : f (genericPoint S) = genericPoint T :=
    f.map_genericPoint_of_denseRange hf
  let hggeneric : g (genericPoint R) = genericPoint S :=
    g.map_genericPoint_of_denseRange hg
  let hgfgeneric : (g ≫ f) (genericPoint R) = genericPoint T :=
    (g ≫ f).map_genericPoint_of_denseRange hgf
  unfold Scheme.Hom.functionFieldMap
  rw [eqToHom_stalk_eq_stalkCongr T hfgeneric.symm,
    eqToHom_stalk_eq_stalkCongr S hggeneric.symm,
    eqToHom_stalk_eq_stalkCongr T hgfgeneric.symm]
  rw [← CommRingCat.hom_comp]
  rw [Category.assoc]
  rw [Scheme.Hom.stalkMap_congr_point_assoc f
      (genericPoint S) (g (genericPoint R)) hggeneric.symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  have hstalk := TopCat.Presheaf.stalkSpecializes_comp_assoc T.presheaf
    (specializes_of_eq (congrArg (fun z : S => f z) hggeneric))
    (specializes_of_eq hfgeneric)
    (f.stalkMap (g (genericPoint R)) ≫ g.stalkMap (genericPoint R))
  exact congrArg CommRingCat.Hom.hom
    (hstalk.trans (congrArg
      (fun k : T.presheaf.stalk (f (g (genericPoint R))) ⟶
          R.presheaf.stalk (genericPoint R) =>
        T.presheaf.stalkSpecializes (specializes_of_eq hgfgeneric) ≫ k)
      (Scheme.Hom.stalkMap_comp g f (genericPoint R)).symm))

/-- The map from an actual component of a pulled-back cover to the original
cover. -/
noncomputable def pullbackComponentToOriginal
    (f : X ⟶ Y) (W : FiniteEtale Y)
    (Z : FiniteEtale X) (i : Z ⟶ (FiniteEtale.pullback f).obj W) :
    Z.left ⟶ W.left :=
  i.left ≫ Limits.pullback.fst W.hom f

/-- The component-to-original map lies over the given map of bases. -/
theorem pullbackComponentToOriginal_comp
    (f : X ⟶ Y) (W : FiniteEtale Y)
    (Z : FiniteEtale X) (i : Z ⟶ (FiniteEtale.pullback f).obj W) :
    pullbackComponentToOriginal f W Z i ≫ W.hom = Z.hom ≫ f := by
  exact (Category.assoc i.left (Limits.pullback.fst W.hom f) W.hom).trans
    ((congrArg (fun k : Limits.pullback W.hom f ⟶ Y => i.left ≫ k)
      (Limits.pullback.condition (f := W.hom) (g := f))).trans
      ((Category.assoc i.left (Limits.pullback.snd W.hom f) f).symm.trans
        (congrArg (fun k : Z.left ⟶ X => k ≫ f) i.w)))

/-- Every connected component of the pullback of a connected finite-etale
cover along a dense morphism still dominates the original cover. -/
theorem pullbackComponentToOriginal_denseRange
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    (W : FiniteEtale Y) [IsConnected W]
    (Z : FiniteEtale X) [IsConnected Z]
    (i : Z ⟶ (FiniteEtale.pullback f).obj W) :
    DenseRange (pullbackComponentToOriginal f W Z i) := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  let g : Z.left ⟶ W.left := pullbackComponentToOriginal f W Z i
  let zHom : Z.left ⟶ X := Z.hom
  let wHom : W.left ⟶ Y := W.hom
  have hZ : DenseRange zHom := by
    let : IsFiniteEtale zHom := by
      simpa only [zHom] using Z.2
    let : Surjective zHom := IsFiniteEtale.surjective zHom
    exact zHom.surjective.denseRange
  have hW : DenseRange wHom := by
    let : IsFiniteEtale wHom := by
      simpa only [wHom] using W.2
    let : Surjective wHom := IsFiniteEtale.surjective wHom
    exact wHom.surjective.denseRange
  have hZf : DenseRange (zHom ≫ f) := by
    change DenseRange (f.base ∘ zHom.base)
    exact hf.comp hZ f.continuous
  have hgW : g ≫ wHom = zHom ≫ f := by
    simpa only [zHom, wHom] using pullbackComponentToOriginal_comp f W Z i
  have hsource :
      wHom (g (genericPoint Z.left)) = genericPoint Y := by
    change (g ≫ wHom) (genericPoint Z.left) = genericPoint Y
    rw [hgW]
    exact (zHom ≫ f).map_genericPoint_of_denseRange hZf
  have htarget : wHom (genericPoint W.left) = genericPoint Y :=
    wHom.map_genericPoint_of_denseRange hW
  have hgeneric : g (genericPoint Z.left) = genericPoint W.left := by
    symm
    apply (wHom.isDiscrete_preimage_singleton
      (genericPoint Y)).eq_of_specializes
      (genericPoint_specializes (g (genericPoint Z.left)))
    · exact htarget
    · exact hsource
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec W.left).def]
  apply closure_mono
  intro x hx
  rcases hx with rfl
  exact ⟨genericPoint Z.left, hgeneric⟩

/-- The map from a connected pullback component to the original connected
cover sends the generic point to the generic point. -/
theorem pullbackComponentToOriginal_map_genericPoint
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    (W : FiniteEtale Y) [IsConnected W]
    (Z : FiniteEtale X) [IsConnected Z]
    (i : Z ⟶ (FiniteEtale.pullback f).obj W) :
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : IsIntegral Z.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
    pullbackComponentToOriginal f W Z i (genericPoint Z.left) =
      genericPoint W.left := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  exact (pullbackComponentToOriginal f W Z i).map_genericPoint_of_denseRange
    (pullbackComponentToOriginal_denseRange f hf W Z i)

/-- The two maps from the base function field to the function field of an
actual pullback component agree. -/
theorem pullbackComponent_functionFieldMap_compatibility
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    (W : FiniteEtale Y) [IsConnected W]
    (Z : FiniteEtale X) [IsConnected Z]
    (i : Z ⟶ (FiniteEtale.pullback f).obj W) :
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : IsIntegral Z.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
    let g := pullbackComponentToOriginal f W Z i
    let hg := pullbackComponentToOriginal_denseRange f hf W Z i
    letI : Algebra Y.functionField X.functionField :=
      f.functionFieldAlgebraOfDenseRange hf
    letI : Algebra Y.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra X.functionField Z.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Z
    letI : Algebra W.left.functionField Z.left.functionField :=
      g.functionFieldAlgebraOfDenseRange hg
    (algebraMap W.left.functionField Z.left.functionField).comp
        (algebraMap Y.functionField W.left.functionField) =
      (algebraMap X.functionField Z.left.functionField).comp
        (algebraMap Y.functionField X.functionField) := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  let g := pullbackComponentToOriginal f W Z i
  let hg := pullbackComponentToOriginal_denseRange f hf W Z i
  let hW := EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected W
  let hZ := EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected Z
  let hWY : IsIntegral ((Functor.fromPUnit Y).obj W.right) := by
    change IsIntegral Y
    infer_instance
  let hZX : IsIntegral ((Functor.fromPUnit X).obj Z.right) := by
    change IsIntegral X
    infer_instance
  let hWW : IsIntegral ((Functor.id Scheme).obj W.left) := by
    change IsIntegral W.left
    infer_instance
  let hZZ : IsIntegral ((Functor.id Scheme).obj Z.left) := by
    change IsIntegral Z.left
    infer_instance
  let : Algebra Y.functionField X.functionField :=
    f.functionFieldAlgebraOfDenseRange hf
  let : Algebra Y.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra X.functionField Z.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Z
  let : Algebra W.left.functionField Z.left.functionField :=
    g.functionFieldAlgebraOfDenseRange hg
  change
    (@Scheme.Hom.functionFieldMap W.left Z.left g inferInstance
      inferInstance hg).comp
      (@Scheme.Hom.functionFieldMap
        ((Functor.fromPUnit Y).obj W.right)
        ((Functor.id Scheme).obj W.left) W.hom hWY hWW hW) =
    (@Scheme.Hom.functionFieldMap
      ((Functor.fromPUnit X).obj Z.right)
      ((Functor.id Scheme).obj Z.left) Z.hom hZX hZZ hZ).comp
      (@Scheme.Hom.functionFieldMap Y X f inferInstance inferInstance hf)
  let hgW : DenseRange (g ≫ W.hom) := by
    change DenseRange (W.hom.base ∘ g.base)
    exact hW.comp hg W.hom.continuous
  let hZf : DenseRange (Z.hom ≫ f) := by
    change DenseRange (f.base ∘ Z.hom.base)
    exact hf.comp hZ f.continuous
  calc
    _ = (g ≫ W.hom).functionFieldMap hgW := by
      simpa only [hgW] using
        Scheme.Hom.functionFieldMap_comp_of_denseRange W.hom hW g hg
    _ = (Z.hom ≫ f).functionFieldMap hZf := by
      exact functionFieldMap_eq_of_eq _ _
        (pullbackComponentToOriginal_comp f W Z i) _ _
    _ = _ := by
      symm
      simpa only [hZf] using
        Scheme.Hom.functionFieldMap_comp_of_denseRange f hf Z.hom hZ

/-- The two function fields generate the function field of an actual
connected component of the pulled-back finite-etale cover. -/
theorem pullbackComponentFunctionFieldProductMap_surjective
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : DenseRange f)
    (W : FiniteEtale Y) [IsConnected W]
    (Z : FiniteEtale X) [IsConnected Z]
    (i : Z ⟶ (FiniteEtale.pullback f).obj W) [Mono i] :
    letI : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    letI : IsIntegral Z.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
    let g := pullbackComponentToOriginal f W Z i
    let hg := pullbackComponentToOriginal_denseRange f hf W Z i
    letI : Algebra Y.functionField X.functionField :=
      f.functionFieldAlgebraOfDenseRange hf
    letI : Algebra Y.functionField W.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    letI : Algebra X.functionField Z.left.functionField :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Z
    letI : Algebra W.left.functionField Z.left.functionField :=
      g.functionFieldAlgebraOfDenseRange hg
    letI : Algebra Y.functionField Z.left.functionField :=
      ((algebraMap X.functionField Z.left.functionField).comp
        (algebraMap Y.functionField X.functionField)).toAlgebra
    letI : IsScalarTower Y.functionField X.functionField
        Z.left.functionField := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Y.functionField W.left.functionField
        Z.left.functionField := IsScalarTower.of_algebraMap_eq'
      (pullbackComponent_functionFieldMap_compatibility f hf W Z i).symm
    Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom Y.functionField X.functionField
          Z.left.functionField)
        (IsScalarTower.toAlgHom Y.functionField W.left.functionField
          Z.left.functionField)) := by
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let : IsIntegral Z.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Z
  let g := pullbackComponentToOriginal f W Z i
  let hg := pullbackComponentToOriginal_denseRange f hf W Z i
  let : Algebra Y.functionField X.functionField :=
    f.functionFieldAlgebraOfDenseRange hf
  let : Algebra Y.functionField W.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : Algebra X.functionField Z.left.functionField :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra Z
  let : Algebra W.left.functionField Z.left.functionField :=
    g.functionFieldAlgebraOfDenseRange hg
  let : Algebra Y.functionField Z.left.functionField :=
    ((algebraMap X.functionField Z.left.functionField).comp
      (algebraMap Y.functionField X.functionField)).toAlgebra
  let : IsScalarTower Y.functionField X.functionField
      Z.left.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Y.functionField W.left.functionField
      Z.left.functionField := IsScalarTower.of_algebraMap_eq'
    (pullbackComponent_functionFieldMap_compatibility f hf W Z i).symm
  obtain ⟨_, hiClosed⟩ :=
    (_root_.AlgebraicGeometry.FiniteEtale.mono_iff X Z
      ((FiniteEtale.pullback f).obj W) i).mp (inferInstance : Mono i)
  let : IsClosedImmersion i.left := hiClosed
  let z' : Z.left ⟶ X := i.left ≫ Limits.pullback.snd W.hom f
  have hz'eq : z' = Z.hom := by
    change i.left ≫ ((FiniteEtale.pullback f).obj W).hom = Z.hom
    exact i.w
  let zHom : Z.left ⟶ X := Z.hom
  let hZ : DenseRange zHom := by
    change DenseRange Z.hom
    exact EtaleFundamentalGroups.finiteEtale_hom_denseRange_of_isConnected Z
  let hz' : DenseRange z' := by
    rw [hz'eq]
    exact hZ
  have hz'Map : z'.functionFieldMap hz' =
      algebraMap X.functionField Z.left.functionField := by
    change z'.functionFieldMap hz' = zHom.functionFieldMap hZ
    exact functionFieldMap_eq_of_eq z' zHom hz'eq hz' hZ
  let t : ((FiniteEtale.pullback f).obj W).left :=
    i.left (genericPoint Z.left)
  let T := Scheme.Pullback.Triplet.ofPoint t
  let : IsArtinianRing T.tensor := by
    simpa only [T, t] using
      pullbackComponent_genericPoint_tensor_isArtinian f hf W Z i
  have hTensorSurjective : Function.Surjective
      (Scheme.Pullback.tensorProductToResidueField t) :=
    Scheme.Pullback.tensorProductToResidueField_surjective_of_isArtinian t
  refine
    @Scheme.Pullback.functionFieldProductMap_surjective_of_pullback_generic_residue
      X W.left Y Z.left
      (inferInstance : IsIntegral X) (inferInstance : IsIntegral W.left)
      (inferInstance : IsIntegral Y) (inferInstance : IsIntegral Z.left)
      f W.hom i.left hiClosed hz' hg
      (inferInstance : Algebra Y.functionField X.functionField)
      (inferInstance : Algebra Y.functionField W.left.functionField)
      (inferInstance : Algebra Y.functionField Z.left.functionField)
      (IsScalarTower.toAlgHom Y.functionField X.functionField
        Z.left.functionField)
      (IsScalarTower.toAlgHom Y.functionField W.left.functionField
        Z.left.functionField) ?_ ?_ ?_
  · change algebraMap X.functionField Z.left.functionField =
      z'.functionFieldMap hz'
    exact hz'Map.symm
  · change algebraMap W.left.functionField Z.left.functionField =
      g.functionFieldMap hg
    rfl
  · exact hTensorSurjective

end AlgebraicGeometry.FiniteEtale

end
