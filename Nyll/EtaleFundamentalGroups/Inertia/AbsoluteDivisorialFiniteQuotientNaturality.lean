/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientCompatibility
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverNormalizationAction

/-!
# Absolute divisorial inertia in finite pointed quotients

This file isolates the arrow-level naturality needed to identify the finite
pointed quotient of the absolute generic Galois map with ordinary restriction
to the function field selected by the fiber point.  Keeping this comparison at
the level of generic lifts avoids unfolding the absolute map while constructing
the induced function-field homomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem fieldGeometricPoint_comp_genericExtensionMorphism'
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Omega := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

private theorem fiberObjEquivHom_eqToIso_left'
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    {U : Scheme.{u}}
    {xi xi' : Spec (.of Omega) ⟶ U} (h : xi = xi')
    (W : FiniteEtale U) (w : (fiber xi).obj W) :
    (fiberObjEquivHom xi' W
        ((eqToIso (congrArg fiber h)).hom.app W w)).left =
      (fiberObjEquivHom xi W w).left := by
  subst xi'
  rfl

private theorem fiberObjEquivHom_eqToIso_inv_left'
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    {U : Scheme.{u}}
    {xi xi' : Spec (.of Omega) ⟶ U} (h : xi = xi')
    (W : FiniteEtale U) (w : (fiber xi').obj W) :
    (fiberObjEquivHom xi W
        ((eqToIso (congrArg fiber h)).inv.app W w)).left =
      (fiberObjEquivHom xi' W w).left := by
  subst xi'
  rfl

private theorem absoluteGaloisFiberAction_left'
    {K Omega : Type u} [Field K] [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega] [IsSepClosed Omega]
    (W : FiniteEtale (Spec (.of K)))
    (y : (fiber (ξ K Omega)).obj W)
    (sigma : Gal(Omega/K)) :
    (fiberObjEquivHom (ξ K Omega) W
      ((absoluteGaloisToFiberAutMulEquiv K Omega
        (IsSepClosure.sep_closed K) sigma).hom.app W y)).left =
      Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫
        (fiberObjEquivHom (ξ K Omega) W y).left := by
  rw [absoluteGaloisToFiberAutMulEquiv,
    CategoryTheory.PreGaloisCategory.toAutMulEquiv_apply,
    CategoryTheory.PreGaloisCategory.toAut_hom_app_apply]
  rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
  rfl

private theorem genericPointLiftPrecomp_left'
    {U : Scheme.{u}} [IsIntegral U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    [IsSepClosed Omega]
    (W : FiniteEtale U)
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma)
    (sigma : Gal(Omega/U.functionField)) :
    Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫ g.left =
      (genericPointLiftPrecomp W g sigma).left := by
  let baseIso :
      (Over.mk (U.genericExtensionMorphism Omega)).left ≅ Spec (.of Omega) :=
    eqToIso (Over.mk_left (U.genericExtensionMorphism Omega))
  apply (cancel_epi baseIso.inv).1
  change
    Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫
        (baseIso.inv ≫ g.left) =
      baseIso.inv ≫ (genericPointLiftPrecomp W g sigma).left
  symm
  change
    (eqToIso (Over.mk_left (U.genericExtensionMorphism Omega))).inv ≫
        (genericPointLiftPrecomp W g sigma).left = _
  rfl

private theorem fundamentalGroupHom_absoluteGalois_left'
    {K Omega : Type u} [Field K] [Field Omega]
    [Algebra K Omega] [IsSepClosure K Omega] [IsSepClosed Omega]
    {U : Scheme.{u}} (f : Spec (.of K) ⟶ U)
    (W : FiniteEtale U)
    (x : (fiber (ξ K Omega ≫ f)).obj W)
    (sigma : Gal(Omega/K)) :
    (fiberObjEquivHom (ξ K Omega ≫ f) W
      ((fundamentalGroupHom f (ξ K Omega)
        (absoluteGaloisToFiberAutMulEquiv K Omega
          (IsSepClosure.sep_closed K) sigma)).hom.app W x)).left =
      Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫
        (fiberObjEquivHom (ξ K Omega ≫ f) W x).left := by
  let eta := ξ K Omega
  let p := pullbackFiberIso f eta
  let a := absoluteGaloisToFiberAutMulEquiv K Omega
    (IsSepClosure.sep_closed K) sigma
  let s : Spec (.of Omega) ⟶ Spec (.of Omega) :=
    Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  let y : (fiber eta).obj ((pullback f).obj W) := p.inv.app W x
  have hp : p.hom.app W y = x :=
    FintypeCat.inv_hom_id_apply (p.app W) x
  have hfund :
      (fundamentalGroupHom f eta a).hom.app W x =
        p.hom.app W (a.hom.app ((pullback f).obj W) y) := by
    have h := pullbackFiberIso_hom_fundamentalGroupHom_apply
      f eta a W y
    rw [hp] at h
    exact h.symm
  have hrecover :
      (fiberObjEquivHom (eta ≫ f) W x).left =
        (fiberObjEquivHom eta ((pullback f).obj W) y).left ≫
          Limits.pullback.fst W.hom f := by
    have h := pullbackFiberIso_hom_fiberObjEquivHom_left f eta W y
    rw [hp] at h
    exact h
  change (fiberObjEquivHom (eta ≫ f) W
    ((fundamentalGroupHom f eta a).hom.app W x)).left =
      s ≫ (fiberObjEquivHom (eta ≫ f) W x).left
  rw [hrecover]
  calc
    _ = (fiberObjEquivHom (eta ≫ f) W
          (p.hom.app W (a.hom.app ((pullback f).obj W) y))).left := by
      rw [hfund]
    _ = (s ≫ (fiberObjEquivHom eta ((pullback f).obj W) y).left) ≫
          Limits.pullback.fst W.hom f := by
      rw [pullbackFiberIso_hom_fiberObjEquivHom_left]
      dsimp only [eta, s, a]
      rw [absoluteGaloisFiberAction_left']
    _ = s ≫
          ((fiberObjEquivHom eta ((pullback f).obj W) y).left ≫
            Limits.pullback.fst W.hom f) := Category.assoc _ _ _

/-- Re-express a lift after replacing its displayed base-point morphism by
an equal morphism.  The underlying scheme arrow is unchanged; in particular,
this avoids transporting a fiber element through an `eqToIso`. -/
noncomputable def genericPointLiftRebase
    {U : Scheme.{u}}
    {Omega : Type u} [Field Omega]
    {xi xi' : Spec (.of Omega) ⟶ U}
    (h : xi = xi') (W : FiniteEtale U)
    (g : Over.mk xi ⟶ W.toComma) :
    Over.mk xi' ⟶ W.toComma :=
  Over.homMk g.left (by
    change g.left ≫ W.hom = xi'
    rw [← h]
    exact g.w)

@[simp]
theorem genericPointLiftRebase_left
    {U : Scheme.{u}}
    {Omega : Type u} [Field Omega]
    {xi xi' : Spec (.of Omega) ⟶ U}
    (h : xi = xi') (W : FiniteEtale U)
    (g : Over.mk xi ⟶ W.toComma) :
    (genericPointLiftRebase h W g).left = g.left := rfl

/-- Acting on a selected fiber point by the pointed finite quotient is the
same as postcomposing its generic lift by the corresponding deck
transformation. -/
theorem finiteEtaleGaloisCoverQuotient_lift_left
    {U : Scheme.{u}} [ConnectedSpace U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U)
    (W : FiniteEtale U) [IsGalois W]
    (w : (fiber xi).obj W) (gamma : π₁ᵉᵗ(xi)) :
    (fiberObjEquivHom xi W w).left ≫
        (finiteEtaleGaloisCoverQuotientMonoidHom
          xi W ‹IsGalois W› w gamma).unop.hom.hom.left =
      (fiberObjEquivHom xi W (gamma.hom.app W w)).left := by
  have heval :
      (fiber xi).map
          (finiteEtaleGaloisCoverQuotientMonoidHom
            xi W ‹IsGalois W› w gamma).unop.hom w = gamma • w :=
    finiteEtaleGaloisCoverQuotientMonoidHom_evaluation
      xi W ‹IsGalois W› w gamma
  have hnat := congrArg (fun q ↦ q.left)
    (fiberObjEquivHom_naturality xi
      (finiteEtaleGaloisCoverQuotientMonoidHom
        xi W ‹IsGalois W› w gamma).unop.hom w)
  rw [heval] at hnat
  change (fiberObjEquivHom xi W w).left ≫
    (finiteEtaleGaloisCoverQuotientMonoidHom
      xi W ‹IsGalois W› w gamma).unop.hom.hom.left = _
  exact hnat

/-- At a composite generic base point, the pointed quotient of the
fundamental-group image of an absolute Galois element acts on the same
underlying generic lift by precomposition.  The lift is rebased by equality
of scheme morphisms rather than by transporting a dependent fiber element. -/
theorem
    finiteEtaleGaloisCoverQuotient_fundamentalGroupHom_absoluteGalois_rebased_lift
    {U : Scheme.{u}} [IsIntegral U] [ConnectedSpace U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    (hf : ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField =
        U.genericExtensionMorphism Omega)
    (W : FiniteEtale U) (hW : IsGalois W)
    (x : (fiber (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField)).obj W)
    (sigma : Gal(Omega/U.functionField)) :
    let g := genericPointLiftRebase hf W
      (fiberObjEquivHom (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W x)
    let gamma := fundamentalGroupHom
      (U.genericExtensionMorphism U.functionField)
      (ξ U.functionField Omega)
      (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
        (IsSepClosure.sep_closed U.functionField) sigma)
    let deck := finiteEtaleGaloisCoverQuotientMonoidHom
      (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W hW x gamma
    g ≫ deck.unop.hom.hom = genericPointLiftPrecomp W g sigma := by
  let : IsGalois W := hW
  let g := genericPointLiftRebase hf W
    (fiberObjEquivHom (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField) W x)
  let gamma := fundamentalGroupHom
    (U.genericExtensionMorphism U.functionField)
    (ξ U.functionField Omega)
    (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
      (IsSepClosure.sep_closed U.functionField) sigma)
  let deck := finiteEtaleGaloisCoverQuotientMonoidHom
    (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField) W hW x gamma
  change g ≫ deck.unop.hom.hom = genericPointLiftPrecomp W g sigma
  apply Over.OverMorphism.ext
  rw [← genericPointLiftPrecomp_left' W g sigma]
  change
    (fiberObjEquivHom (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField) W x).left ≫
        deck.unop.hom.hom.left =
      Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫
        (fiberObjEquivHom (ξ U.functionField Omega ≫
          U.genericExtensionMorphism U.functionField) W x).left
  exact
    (finiteEtaleGaloisCoverQuotient_lift_left
      (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W x gamma).trans
      (fundamentalGroupHom_absoluteGalois_left'
        (U.genericExtensionMorphism U.functionField) W x sigma)

/-- The pointed quotient at the direct absolute generic base point acts on
the lift obtained from the composite base point by ordinary precomposition.
Only the quotient element is transported through `absoluteGenericFiberIso`;
the lift itself is rebased with the same underlying scheme arrow. -/
theorem finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_rebased_lift
    {U : Scheme.{u}} [IsIntegral U] [ConnectedSpace U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W)
    (sigma : Gal(Omega/U.functionField)) :
    let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
    let x := (absoluteGenericFiberIso U Omega).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ U.functionField Omega ≫
          U.genericExtensionMorphism U.functionField) W x)
    let deck := finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Omega) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
    g ≫ deck.unop.hom.hom = genericPointLiftPrecomp W g sigma := by
  let : IsGalois W := hW
  let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W x)
  let deck := finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Omega) W hW w
    (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
  let gamma := fundamentalGroupHom
    (U.genericExtensionMorphism U.functionField)
    (ξ U.functionField Omega)
    (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
      (IsSepClosure.sep_closed U.functionField) sigma)
  let deckComposite := finiteEtaleGaloisCoverQuotientMonoidHom
    (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField) W hW x gamma
  have hdeck : deck = deckComposite := by
    exact finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_transport
      Omega W hW w sigma
  change g ≫ deck.unop.hom.hom = genericPointLiftPrecomp W g sigma
  rw [hdeck]
  exact
    finiteEtaleGaloisCoverQuotient_fundamentalGroupHom_absoluteGalois_rebased_lift
      Omega h W hW x sigma

/-- An equality of generic lifts turns a deck transformation into the
corresponding equality of function-field embeddings. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_of_lift_eq
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U) [IsConnected W]
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma)
    (deck : (Aut W)ᵐᵒᵖ)
    (sigma : Gal(Omega/U.functionField))
    (hlift : g ≫ deck.unop.hom.hom =
      genericPointLiftPrecomp W g sigma) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    (finiteEtaleGenericHomFunctionFieldAlgHom W g).comp
        (finiteEtaleAutFunctionFieldAlgEquiv W deck.unop).toAlgHom =
      sigma.toAlgHom.comp
        (finiteEtaleGenericHomFunctionFieldAlgHom W g) := by
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  calc
    _ = finiteEtaleGenericHomFunctionFieldAlgHom W
        (g ≫ deck.unop.hom.hom) :=
      (finiteEtaleGenericHomFunctionFieldAlgHom_comp_aut
        W g deck.unop).symm
    _ = finiteEtaleGenericHomFunctionFieldAlgHom W
      (genericPointLiftPrecomp W g sigma) := by rw [hlift]
    _ = _ := finiteEtaleGenericHomFunctionFieldAlgHom_precomp W g sigma

/-- Relative to the function-field embedding selected by the rebased
composite generic lift, the deck transformation in the direct pointed
quotient is exactly restriction of the absolute Galois element. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_absoluteGenericGalois_rebased
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W)
    (sigma : Gal(Omega/U.functionField)) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
    let x := (absoluteGenericFiberIso U Omega).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ U.functionField Omega ≫
          U.genericExtensionMorphism U.functionField) W x)
    let deck := finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Omega) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
    (finiteEtaleGenericHomFunctionFieldAlgHom W g).comp
        (finiteEtaleAutFunctionFieldAlgEquiv W deck.unop).toAlgHom =
      sigma.toAlgHom.comp
        (finiteEtaleGenericHomFunctionFieldAlgHom W g) := by
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W x)
  let deck := finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Omega) W hW w
    (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
  change
    (finiteEtaleGenericHomFunctionFieldAlgHom W g).comp
        (finiteEtaleAutFunctionFieldAlgEquiv W deck.unop).toAlgHom =
      sigma.toAlgHom.comp
        (finiteEtaleGenericHomFunctionFieldAlgHom W g)
  exact finiteEtaleGenericHomFunctionFieldAlgHom_of_lift_eq
    W g deck sigma
      (finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_rebased_lift
        Omega W hW w sigma)

/-- Relative to the field embedding selected by the rebased generic lift,
the restriction of an absolute Galois element to the cover function field is
literally the function-field automorphism induced by its pointed deck
quotient. -/
theorem restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U] [ConnectedSpace U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W)
    (sigma : Gal(Omega/U.functionField)) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional U.functionField W.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois U.functionField W.left.functionField :=
      isGalois_functionField_of_isGalois_finiteEtale W hW
    let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
    let x := (absoluteGenericFiberIso U Omega).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ U.functionField Omega ≫
          U.genericExtensionMorphism U.functionField) W x)
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    let deck := finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Omega) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
    letI : Algebra W.left.functionField Omega :=
      j.toRingHom.toAlgebra
    letI : IsScalarTower U.functionField W.left.functionField Omega := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    AlgEquiv.restrictNormalHom
        (F := U.functionField) (K₁ := Omega) W.left.functionField sigma =
      finiteEtaleAutFunctionFieldAlgEquiv W deck.unop := by
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional U.functionField W.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois U.functionField W.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale W hW
  let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) W x)
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let deck := finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Omega) W hW w
    (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
  let : Algebra W.left.functionField Omega :=
    j.toRingHom.toAlgebra
  let : IsScalarTower U.functionField W.left.functionField Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  have hintertwine :=
    finiteEtaleGenericHomFunctionFieldAlgHom_absoluteGenericGalois_rebased
      Omega W hW w sigma
  apply AlgEquiv.ext
  intro z
  apply j.injective
  calc
    j (AlgEquiv.restrictNormalHom
        (F := U.functionField) (K₁ := Omega)
        W.left.functionField sigma z) =
        sigma (j z) := by
      exact AlgEquiv.restrictNormal_commutes sigma W.left.functionField z
    _ = j (finiteEtaleAutFunctionFieldAlgEquiv W deck.unop z) := by
      exact (DFunLike.congr_fun hintertwine z).symm

section AbsoluteNormalizationPrime

variable {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
  [IsLocallyNoetherian U] [ConnectedSpace U]
variable (Omega : Type u) [Field Omega]
  [Algebra U.functionField Omega]
  [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Algebra A U.functionField] [IsFractionRing A U.functionField]
  [Algebra A Omega] [IsScalarTower A U.functionField Omega]

local instance absoluteNormalizationPrimeAction :
    MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
  IsIntegralClosure.MulSemiringAction A U.functionField Omega
    (integralClosure A Omega)

/-- Absolute normalization-prime inertia membership descends to membership
of the corresponding direct pointed deck element in ideal inertia at the
contracted prime.  The contraction uses the function-field embedding selected
by the rebased generic lift. -/
theorem finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_mem_contractedIdealInertia
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W)
    (sigma : Gal(Omega/U.functionField))
    (hsigma : sigma ∈
      Q.toAddSubgroup.inertia Gal(Omega/U.functionField)) :
    letI : IsGalois W := hW
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    let K := U.functionField
    let L := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale W hW
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
    let x := (absoluteGenericFiberIso U Omega).inv.app W w
    let g := genericPointLiftRebase h W
      (fiberObjEquivHom
        (ξ K Omega ≫ U.genericExtensionMorphism K) W x)
    let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
    let deck := finiteEtaleGaloisCoverQuotientMonoidHom
      (U.genericExtensionMorphism Omega) W hW w
      (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
    letI : Algebra L Omega := j.toRingHom.toAlgebra
    letI : IsScalarTower K L Omega := by
      apply IsScalarTower.of_algebraMap_eq'
      ext z
      exact (j.commutes z).symm
    letI : IsScalarTower A L Omega := by
      apply IsScalarTower.of_algebraMap_eq'
      ext a
      change algebraMap A Omega a = j (algebraMap A L a)
      calc
        algebraMap A Omega a =
            algebraMap K Omega (algebraMap A K a) :=
          IsScalarTower.algebraMap_apply A K Omega a
        _ = j (algebraMap K L (algebraMap A K a)) :=
          (j.commutes (algebraMap A K a)).symm
        _ = j (algebraMap A L a) := by
          rw [IsScalarTower.algebraMap_apply A K L]
    let B := integralClosure A L
    let QL := absoluteNormalizationPrimeContraction
      (A := A) (L := L) (Omega := Omega) Q
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction A K L B
    letI : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
      Kummer.finiteEtaleGaloisCoverNormalizationAction W hW A B
    deck ∈ QL.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ := by
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale W hW
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let h := fieldGeometricPoint_comp_genericExtensionMorphism' U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ K Omega ≫ U.genericExtensionMorphism K) W x)
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let deck := finiteEtaleGaloisCoverQuotientMonoidHom
    (U.genericExtensionMorphism Omega) W hW w
    (absoluteGenericGaloisToFundamentalGroup U Omega sigma)
  let : Algebra L Omega := j.toRingHom.toAlgebra
  let : IsScalarTower K L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : IsScalarTower A L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A Omega a = j (algebraMap A L a)
    calc
      algebraMap A Omega a =
          algebraMap K Omega (algebraMap A K a) :=
        IsScalarTower.algebraMap_apply A K Omega a
      _ = j (algebraMap K L (algebraMap A K a)) :=
        (j.commutes (algebraMap A K a)).symm
      _ = j (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K L]
  let B := integralClosure A L
  let QL := absoluteNormalizationPrimeContraction
    (A := A) (L := L) (Omega := Omega) Q
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
    Kummer.finiteEtaleGaloisCoverNormalizationAction W hW A B
  have hrestrict :=
    restrictNormalHom_eq_finiteEtaleAutFunctionFieldAlgEquiv_absoluteGenericGalois_rebased
      Omega W hW w sigma
  have hfield :
      finiteEtaleAutOpFunctionFieldMulEquiv W hW deck ∈
        QL.toAddSubgroup.inertia Gal(L/K) := by
    rw [finiteEtaleAutOpFunctionFieldMulEquiv_apply, ← hrestrict]
    apply absoluteNormalizationPrime_inertia_map_le_contraction
      (A := A) (K := K) (L := L) (Omega := Omega) Q
    exact ⟨sigma, hsigma, rfl⟩
  change deck ∈ QL.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ
  intro b
  rw [← Kummer.finiteEtaleGaloisCoverNormalizationAction_smul
    W hW A B deck b]
  exact hfield b

end AbsoluteNormalizationPrime

end EtaleFundamentalGroups.Inertia

end
