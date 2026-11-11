/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
public import Nyll.SchemeTheory.FunctionFields.Functoriality

/-!
# Function fields of connected finite-etale covers

A connected finite-etale cover of a normal integral scheme
has a canonical finite separable extension of function fields.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- The structure morphism of a connected finite-etale cover of an integral
scheme has dense image. -/
theorem finiteEtale_hom_denseRange_of_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] : DenseRange Y.hom := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : IsFiniteEtale Y.hom := Y.2
  let : PreconnectedSpace ↑((Functor.fromPUnit X).obj Y.right) := by
    change PreconnectedSpace X
    infer_instance
  let : Nonempty ((Functor.id Scheme).obj Y.left) := by
    change Nonempty Y.left
    infer_instance
  let : Surjective Y.hom := IsFiniteEtale.surjective Y.hom
  exact Y.hom.surjective.denseRange

/-- The canonical algebra structure on the function field of a connected
finite-etale cover. -/
@[reducible] noncomputable def finiteEtaleFunctionFieldAlgebra
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    Algebra X.functionField Y.left.functionField := by
  intro sharedDefinitionOwner1
  exact ((show Y.left ⟶ X from Y.hom).functionFieldMap
    (finiteEtale_hom_denseRange_of_isConnected Y)).toAlgebra

/-- The canonical function-field map of a connected finite-etale cover is
essentially of finite type. -/
theorem finiteEtale_functionFieldMap_essFiniteType
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).EssFiniteType := by
  intro sharedOwner1
  let : IsFiniteEtale (show Y.left ⟶ X from Y.hom) := Y.2
  unfold Scheme.Hom.functionFieldMap
  rw [CommRingCat.hom_comp,
    RingHom.EssFiniteType.respectsIso.cancel_left_isIso]
  exact LocallyOfFiniteType.stalkMap
    (show Y.left ⟶ X from Y.hom) (genericPoint Y.left)

/-- The canonical function-field map of a connected finite-etale cover is
formally unramified. -/
theorem finiteEtale_functionFieldMap_formallyUnramified
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).FormallyUnramified := by
  intro sharedOwner1
  let : IsFiniteEtale (show Y.left ⟶ X from Y.hom) := Y.2
  unfold Scheme.Hom.functionFieldMap
  rw [CommRingCat.hom_comp,
    RingHom.FormallyUnramified.respectsIso.cancel_left_isIso]
  exact FormallyUnramified.stalkMap
    (show Y.left ⟶ X from Y.hom) (genericPoint Y.left)

/-- A connected finite-etale cover induces a finite-dimensional extension of
function fields. -/
theorem finiteDimensional_functionField_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    FiniteDimensional X.functionField Y.left.functionField := by
  intro sharedOwner1 sharedOwner2
  let : Algebra.EssFiniteType X.functionField Y.left.functionField := by
    apply RingHom.essFiniteType_algebraMap.mp
    change ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).EssFiniteType
    exact finiteEtale_functionFieldMap_essFiniteType Y
  let : Algebra.FormallyUnramified X.functionField Y.left.functionField := by
    apply RingHom.formallyUnramified_algebraMap.mp
    change ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).FormallyUnramified
    exact finiteEtale_functionFieldMap_formallyUnramified Y
  exact Algebra.FormallyUnramified.finite_of_free
    X.functionField Y.left.functionField

/-- A connected finite-etale cover induces a separable extension of function
fields. -/
theorem isSeparable_functionField_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Algebra.IsSeparable X.functionField Y.left.functionField := by
  intro sharedOwner1 sharedOwner2
  let : Algebra.EssFiniteType X.functionField Y.left.functionField := by
    apply RingHom.essFiniteType_algebraMap.mp
    change ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).EssFiniteType
    exact finiteEtale_functionFieldMap_essFiniteType Y
  let : Algebra.FormallyUnramified X.functionField Y.left.functionField := by
    apply RingHom.formallyUnramified_algebraMap.mp
    change ((show Y.left ⟶ X from Y.hom).functionFieldMap
      (finiteEtale_hom_denseRange_of_isConnected Y)).FormallyUnramified
    exact finiteEtale_functionFieldMap_formallyUnramified Y
  exact Algebra.FormallyUnramified.isSeparable
    X.functionField Y.left.functionField

/-- A connected finite étale cover of an integral normal base has integral source.
Cover comparisons retain this proof for their chosen cover. -/
theorem coverIntegral
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] : IsIntegral Y.left :=
  isIntegral_left_of_isConnected_finiteEtale Y

/-- The canonical function-field algebra retained by cover comparisons. -/
@[reducible] def coverFieldAlgebra
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left := coverIntegral Y
    Algebra X.functionField Y.left.functionField := by
  intro integralCover
  exact finiteEtaleFunctionFieldAlgebra Y

/-- The canonical finite-dimensional function-field extension of a connected cover. -/
theorem coverFieldFinite
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    let : IsIntegral Y.left := coverIntegral Y
    let : Algebra X.functionField Y.left.functionField :=
      coverFieldAlgebra Y
    FiniteDimensional X.functionField Y.left.functionField := by
  intro integralCover coverAlgebra
  exact finiteDimensional_functionField_of_finiteEtale_isConnected Y

end EtaleFundamentalGroups
