/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-!
# Function fields of finite-etale Galois covers

This file compares the generic geometric fiber of a connected finite-etale
cover with embeddings of its function field.  It then transports categorical
Galoisness to the resulting finite separable field extension.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  exact (Z.presheaf.stalkSpecializes_refl z).symm

private noncomputable def genericPointFunctionFieldMap
    (Z : Scheme.{u}) [IsIntegral Z]
    {Ω : Type u} [Field Ω]
    (q : Spec (.of Ω) ⟶ Z)
    (hq : q (IsLocalRing.closedPoint Ω) = genericPoint Z) :
    Z.functionField →+* Ω :=
  ((Z.presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
    Scheme.stalkClosedPointTo q).hom

private theorem genericPointFunctionFieldMap_comp
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : Z ⟶ X) (hf : DenseRange f)
    {Ω : Type u} [Field Ω]
    (q : Spec (.of Ω) ⟶ Z)
    (hq : q (IsLocalRing.closedPoint Ω) = genericPoint Z) :
    let hqf : (q ≫ f) (IsLocalRing.closedPoint Ω) = genericPoint X := by
      exact (congrArg (fun z : Z => f z) hq).trans
        (f.map_genericPoint_of_denseRange hf)
    (genericPointFunctionFieldMap Z q hq).comp
        (f.functionFieldMap hf) =
      genericPointFunctionFieldMap X (q ≫ f) hqf := by
  let hgeneric : f (genericPoint Z) = genericPoint X :=
    f.map_genericPoint_of_denseRange hf
  let hqf : (q ≫ f) (IsLocalRing.closedPoint Ω) = genericPoint X := by
    exact (congrArg (fun z : Z => f z) hq).trans hgeneric
  change (genericPointFunctionFieldMap Z q hq).comp
      (f.functionFieldMap hf) = genericPointFunctionFieldMap X (q ≫ f) hqf
  unfold genericPointFunctionFieldMap Scheme.Hom.functionFieldMap
  rw [eqToHom_stalk_eq_stalkCongr X hgeneric.symm]
  rw [← CommRingCat.hom_comp]
  rw [Category.assoc, Scheme.Hom.stalkMap_congr_point_assoc f
    (genericPoint Z) (q (IsLocalRing.closedPoint Ω)) hq.symm]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  have hstalk := TopCat.Presheaf.stalkSpecializes_comp_assoc X.presheaf
    (specializes_of_eq (congrArg (fun z : Z => f z) hq))
    (specializes_of_eq hgeneric)
    (f.stalkMap (q (IsLocalRing.closedPoint Ω)) ≫ Scheme.stalkClosedPointTo q)
  exact congrArg CommRingCat.Hom.hom
    (hstalk.trans (congrArg
      (fun k : X.presheaf.stalk (f (q (IsLocalRing.closedPoint Ω))) ⟶ CommRingCat.of Ω =>
        X.presheaf.stalkSpecializes (specializes_of_eq hqf) ≫ k)
      (Scheme.stalkClosedPointTo_comp (f := q) f).symm))

private theorem stalkMap_eq_of_congr_maps
    (Z : Scheme.{u}) {x₁ x₂ x : Z} (h₁ : x₁ = x) (h₂ : x₂ = x)
    {A : CommRingCat} (f₁ : Z.presheaf.stalk x₁ ⟶ A)
    (f₂ : Z.presheaf.stalk x₂ ⟶ A)
    (hmaps :
      (Z.presheaf.stalkCongr (.of_eq h₁.symm)).hom ≫ f₁ =
        (Z.presheaf.stalkCongr (.of_eq h₂.symm)).hom ≫ f₂) :
    f₁ = (Z.presheaf.stalkCongr (.of_eq (h₁.trans h₂.symm))).hom ≫ f₂ := by
  cases h₁
  cases h₂
  simpa using hmaps

private theorem genericPointMorphism_eq_of_stalkMap_eq
    (Z : Scheme.{u}) [IsIntegral Z]
    {Ω : Type u} [Field Ω]
    (q₁ q₂ : Spec (.of Ω) ⟶ Z)
    (hq₁ : q₁ (IsLocalRing.closedPoint Ω) = genericPoint Z)
    (hq₂ : q₂ (IsLocalRing.closedPoint Ω) = genericPoint Z)
    (hmaps :
      (Z.presheaf.stalkCongr (.of_eq hq₁.symm)).hom ≫
          Scheme.stalkClosedPointTo q₁ =
        (Z.presheaf.stalkCongr (.of_eq hq₂.symm)).hom ≫
          Scheme.stalkClosedPointTo q₂) : q₁ = q₂ := by
  apply (SpecToEquivOfLocalRing Z (CommRingCat.of Ω)).injective
  apply SpecToEquivOfLocalRing_eq_iff.mpr
  let hp : q₁ (IsLocalRing.closedPoint Ω) =
      q₂ (IsLocalRing.closedPoint Ω) := hq₁.trans hq₂.symm
  refine ⟨hp, ?_⟩
  change Scheme.stalkClosedPointTo q₁ =
    (Z.presheaf.stalkCongr (.of_eq hp)).hom ≫
      Scheme.stalkClosedPointTo q₂
  exact stalkMap_eq_of_congr_maps Z hq₁ hq₂
    (Scheme.stalkClosedPointTo q₁) (Scheme.stalkClosedPointTo q₂) hmaps

private noncomputable def finiteEtaleGenericHom
    {X : Scheme.{u}} [IsIntegral X]
    (Y : FiniteEtale X)
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    Spec (.of Ω) ⟶ Y.left :=
  (eqToIso (Over.mk_left (X.genericExtensionMorphism Ω))).inv ≫ g.left

private theorem finiteEtaleGenericHom_comp
    {X : Scheme.{u}} [IsIntegral X]
    (Y : FiniteEtale X)
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    finiteEtaleGenericHom Y g ≫ Y.hom = X.genericExtensionMorphism Ω := by
  let baseIso :
      (Over.mk (X.genericExtensionMorphism Ω)).left ≅ Spec (.of Ω) :=
    eqToIso (Over.mk_left (X.genericExtensionMorphism Ω))
  have baseIso_hom_comp :
      baseIso.hom ≫ X.genericExtensionMorphism Ω =
        (Over.mk (X.genericExtensionMorphism Ω)).hom := by
    change eqToHom (Over.mk_left (X.genericExtensionMorphism Ω)) ≫
        X.genericExtensionMorphism Ω =
      (Over.mk (X.genericExtensionMorphism Ω)).hom
    exact eq_of_heq (eqToHom_comp_heq (X.genericExtensionMorphism Ω)
      (Over.mk_left (X.genericExtensionMorphism Ω)))
  have gw : g.left ≫ Y.hom =
      (Over.mk (X.genericExtensionMorphism Ω)).hom := by
    exact g.w
  change (baseIso.inv ≫ g.left) ≫ Y.hom =
    X.genericExtensionMorphism Ω
  calc
    (baseIso.inv ≫ g.left) ≫ Y.hom =
        baseIso.inv ≫ (g.left ≫ Y.hom) := Category.assoc _ _ _
    _ = baseIso.inv ≫ (Over.mk (X.genericExtensionMorphism Ω)).hom :=
      congrArg (fun q ↦ baseIso.inv ≫ q) gw
    _ = baseIso.inv ≫
        (baseIso.hom ≫ X.genericExtensionMorphism Ω) :=
      congrArg (fun q ↦ baseIso.inv ≫ q) baseIso_hom_comp.symm
    _ = X.genericExtensionMorphism Ω :=
      baseIso.inv_hom_id_assoc _

private theorem finiteEtale_genericPoint_of_over_genericExtension
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    finiteEtaleGenericHom Y g (IsLocalRing.closedPoint Ω) =
      genericPoint Y.left := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let f : Y.left ⟶ X := Y.hom
  let : IsFiniteEtale f := Y.2
  have hg :
      f (finiteEtaleGenericHom Y g (IsLocalRing.closedPoint Ω)) =
        genericPoint X := by
    have hcomp : finiteEtaleGenericHom Y g ≫ f =
        X.genericExtensionMorphism Ω := by
      change finiteEtaleGenericHom Y g ≫ Y.hom =
        X.genericExtensionMorphism Ω
      exact finiteEtaleGenericHom_comp Y g
    calc
      f (finiteEtaleGenericHom Y g (IsLocalRing.closedPoint Ω)) =
          (finiteEtaleGenericHom Y g ≫ f) (IsLocalRing.closedPoint Ω) :=
        (Scheme.Hom.comp_apply _ _ _).symm
      _ = (X.genericExtensionMorphism Ω) (IsLocalRing.closedPoint Ω) :=
        congrArg (fun h : Spec (.of Ω) ⟶ X => h (IsLocalRing.closedPoint Ω)) hcomp
      _ = genericPoint X := X.genericExtensionMorphism_apply_closedPoint Ω
  have hgeneric : f (genericPoint Y.left) = genericPoint X :=
    f.map_genericPoint_of_denseRange
      (finiteEtale_hom_denseRange_of_isConnected Y)
  symm
  apply (f.isDiscrete_preimage_singleton (genericPoint X)).eq_of_specializes
    (genericPoint_specializes
      (finiteEtaleGenericHom Y g (IsLocalRing.closedPoint Ω)))
  · exact hgeneric
  · exact hg

/-- The ring map from the function field of a connected finite-etale cover
obtained by evaluating a generic geometric point. -/
noncomputable def finiteEtaleGenericHomFunctionFieldMap
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    Y.left.functionField →+* Ω := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  exact ((Y.left.presheaf.stalkCongr (.of_eq
      (finiteEtale_genericPoint_of_over_genericExtension Y g).symm)).hom ≫
    Scheme.stalkClosedPointTo (finiteEtaleGenericHom Y g)).hom

private theorem stalkClosedPointTo_genericExtensionMorphism
    {X : Scheme.{u}} [IsIntegral X]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω] :
    (X.presheaf.stalkCongr (.of_eq
      (X.genericExtensionMorphism_apply_closedPoint Ω).symm)).hom ≫
      Scheme.stalkClosedPointTo (X.genericExtensionMorphism Ω) =
      CommRingCat.ofHom (algebraMap X.functionField Ω) := by
  let z : Σ x, { f : X.presheaf.stalk x ⟶ CommRingCat.of Ω //
      IsLocalHom f.hom } :=
    ⟨genericPoint X,
      ⟨CommRingCat.ofHom (algebraMap X.functionField Ω), inferInstance⟩⟩
  have hz := (SpecToEquivOfLocalRing X (CommRingCat.of Ω)).right_inv z
  obtain ⟨hpoint, hmap⟩ := SpecToEquivOfLocalRing_eq_iff.mp hz
  dsimp [SpecToEquivOfLocalRing, z] at hpoint hmap
  unfold Scheme.genericExtensionMorphism
  let e := X.presheaf.stalkCongr (Inseparable.of_eq hpoint)
  exact (congrArg (fun k => e.inv ≫ k) hmap).trans
    (e.inv_hom_id_assoc (CommRingCat.ofHom (algebraMap X.functionField Ω)))

private theorem stalkClosedPointTo_of_eq_genericExtensionMorphism
    {X : Scheme.{u}} [IsIntegral X]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (r : Spec (.of Ω) ⟶ X)
    (hr : r = X.genericExtensionMorphism Ω)
    (hpoint : r (IsLocalRing.closedPoint Ω) = genericPoint X) :
    (X.presheaf.stalkCongr (.of_eq hpoint.symm)).hom ≫
        Scheme.stalkClosedPointTo r =
      CommRingCat.ofHom (algebraMap X.functionField Ω) := by
  subst r
  exact stalkClosedPointTo_genericExtensionMorphism

private theorem finiteEtaleGenericHomFunctionFieldMap_comp
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (finiteEtaleGenericHomFunctionFieldMap Y g).comp
        (algebraMap X.functionField Y.left.functionField) =
      algebraMap X.functionField Ω := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let f : Y.left ⟶ X := Y.hom
  let q : Spec (CommRingCat.of Ω) ⟶ Y.left := finiteEtaleGenericHom Y g
  have hq : q (IsLocalRing.closedPoint Ω) = genericPoint Y.left :=
    finiteEtale_genericPoint_of_over_genericExtension Y g
  have hqf : (q ≫ f) (IsLocalRing.closedPoint Ω) = genericPoint X :=
    (congrArg (fun z : Y.left => f z) hq).trans
      (f.map_genericPoint_of_denseRange
        (finiteEtale_hom_denseRange_of_isConnected Y))
  change (genericPointFunctionFieldMap Y.left q hq).comp
    (f.functionFieldMap (finiteEtale_hom_denseRange_of_isConnected Y)) = _
  refine (genericPointFunctionFieldMap_comp f
    (finiteEtale_hom_denseRange_of_isConnected Y) q hq).trans ?_
  exact congrArg CommRingCat.Hom.hom
    (stalkClosedPointTo_of_eq_genericExtensionMorphism (q ≫ f)
      (finiteEtaleGenericHom_comp Y g) hqf)

/-- A generic geometric point of a connected finite-etale cover gives an
embedding of its function field over the function field of the base. -/
noncomputable def finiteEtaleGenericHomFunctionFieldAlgHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Y.left.functionField →ₐ[X.functionField] Ω := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact
    { __ := finiteEtaleGenericHomFunctionFieldMap Y g
      commutes' := fun z ↦ DFunLike.congr_fun
        (finiteEtaleGenericHomFunctionFieldMap_comp Y g) z }

private theorem finiteEtaleGenericHomFunctionFieldAlgHom_injective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω] :
    Function.Injective
      (finiteEtaleGenericHomFunctionFieldAlgHom (Ω := Ω) Y) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  intro g₁ g₂ h
  let q₁ : Spec (.of Ω) ⟶ Y.left := finiteEtaleGenericHom Y g₁
  let q₂ : Spec (.of Ω) ⟶ Y.left := finiteEtaleGenericHom Y g₂
  have hq₁ : q₁ (IsLocalRing.closedPoint Ω) = genericPoint Y.left :=
    finiteEtale_genericPoint_of_over_genericExtension Y g₁
  have hq₂ : q₂ (IsLocalRing.closedPoint Ω) = genericPoint Y.left :=
    finiteEtale_genericPoint_of_over_genericExtension Y g₂
  have hmaps :
      (Y.left.presheaf.stalkCongr (.of_eq hq₁.symm)).hom ≫
          Scheme.stalkClosedPointTo q₁ =
        (Y.left.presheaf.stalkCongr (.of_eq hq₂.symm)).hom ≫
          Scheme.stalkClosedPointTo q₂ := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h
  have qeq : q₁ = q₂ :=
    genericPointMorphism_eq_of_stalkMap_eq Y.left q₁ q₂ hq₁ hq₂ hmaps
  ext1
  let baseIso :
      (Over.mk (X.genericExtensionMorphism Ω)).left ≅ Spec (.of Ω) :=
    eqToIso (Over.mk_left (X.genericExtensionMorphism Ω))
  apply (cancel_epi baseIso.inv).1
  exact qeq

private theorem finiteEtaleGenericHomFunctionFieldAlgHom_surjective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω] :
    Function.Surjective
      (finiteEtaleGenericHomFunctionFieldAlgHom (Ω := Ω) Y) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  intro a
  let z : Σ y, { f : Y.left.presheaf.stalk y ⟶ CommRingCat.of Ω //
      IsLocalHom f.hom } :=
    ⟨genericPoint Y.left, ⟨CommRingCat.ofHom a.toRingHom, inferInstance⟩⟩
  let q : Spec (.of Ω) ⟶ Y.left :=
    (SpecToEquivOfLocalRing Y.left (CommRingCat.of Ω)).symm z
  have hz :=
    (SpecToEquivOfLocalRing Y.left (CommRingCat.of Ω)).apply_symm_apply z
  obtain ⟨hq, hmap⟩ := SpecToEquivOfLocalRing_eq_iff.mp hz
  dsimp [SpecToEquivOfLocalRing, z] at hq hmap
  change q (IsLocalRing.closedPoint Ω) = genericPoint Y.left at hq
  change Scheme.stalkClosedPointTo q =
    (Y.left.presheaf.stalkCongr (.of_eq hq.symm)).inv ≫
      CommRingCat.ofHom a.toRingHom at hmap
  have hqmap : genericPointFunctionFieldMap Y.left q hq = a.toRingHom := by
    unfold genericPointFunctionFieldMap
    rw [hmap]
    exact congrArg CommRingCat.Hom.hom
      ((Y.left.presheaf.stalkCongr (.of_eq hq.symm)).hom_inv_id_assoc
        (CommRingCat.ofHom a.toRingHom))
  let f : Y.left ⟶ X := Y.hom
  let : IsFiniteEtale f := Y.2
  have hf : DenseRange f := finiteEtale_hom_denseRange_of_isConnected Y
  have hgeneric : f (genericPoint Y.left) = genericPoint X :=
    f.map_genericPoint_of_denseRange hf
  have hqf : (q ≫ f) (IsLocalRing.closedPoint Ω) = genericPoint X := by
    calc
      (q ≫ f) (IsLocalRing.closedPoint Ω) =
          f (q (IsLocalRing.closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
      _ = f (genericPoint Y.left) := congrArg f hq
      _ = genericPoint X := hgeneric
  have hqfMap : genericPointFunctionFieldMap X (q ≫ f) hqf =
      algebraMap X.functionField Ω := by
    rw [← genericPointFunctionFieldMap_comp f hf q hq, hqmap]
    change a.toRingHom.comp
        (algebraMap X.functionField Y.left.functionField) =
      algebraMap X.functionField Ω
    ext x
    exact a.commutes x
  have qcomp : q ≫ f = X.genericExtensionMorphism Ω := by
    apply genericPointMorphism_eq_of_stalkMap_eq X
      (q ≫ f) (X.genericExtensionMorphism Ω) hqf
      (X.genericExtensionMorphism_apply_closedPoint Ω)
    apply CommRingCat.hom_ext
    change genericPointFunctionFieldMap X (q ≫ f) hqf =
      genericPointFunctionFieldMap X (X.genericExtensionMorphism Ω)
        (X.genericExtensionMorphism_apply_closedPoint Ω)
    calc
      _ = algebraMap X.functionField Ω := hqfMap
      _ = _ := (congrArg CommRingCat.Hom.hom
        stalkClosedPointTo_genericExtensionMorphism).symm
  let baseIso :
      (Over.mk (X.genericExtensionMorphism Ω)).left ≅ Spec (.of Ω) :=
    eqToIso (Over.mk_left (X.genericExtensionMorphism Ω))
  have baseIso_hom_comp :
      baseIso.hom ≫ X.genericExtensionMorphism Ω =
        (Over.mk (X.genericExtensionMorphism Ω)).hom := by
    change eqToHom (Over.mk_left (X.genericExtensionMorphism Ω)) ≫
        X.genericExtensionMorphism Ω =
      (Over.mk (X.genericExtensionMorphism Ω)).hom
    exact eq_of_heq (eqToHom_comp_heq (X.genericExtensionMorphism Ω)
      (Over.mk_left (X.genericExtensionMorphism Ω)))
  let g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma :=
    Over.homMk (baseIso.hom ≫ q) (by
      calc
        (baseIso.hom ≫ q) ≫ Y.hom =
            baseIso.hom ≫ (q ≫ f) := Category.assoc _ _ _
        _ = baseIso.hom ≫ X.genericExtensionMorphism Ω :=
          congrArg (fun r ↦ baseIso.hom ≫ r) qcomp
        _ = (Over.mk (X.genericExtensionMorphism Ω)).hom :=
          baseIso_hom_comp)
  refine ⟨g, ?_⟩
  have hqg : finiteEtaleGenericHom Y g = q := by
    change baseIso.inv ≫ (baseIso.hom ≫ q) = q
    exact baseIso.inv_hom_id_assoc q
  apply AlgHom.coe_ringHom_injective
  change finiteEtaleGenericHomFunctionFieldMap Y g = a.toRingHom
  change genericPointFunctionFieldMap Y.left
      (finiteEtaleGenericHom Y g)
      (finiteEtale_genericPoint_of_over_genericExtension Y g) = a.toRingHom
  simpa only [hqg] using hqmap

/-- Generic geometric points of a connected finite-etale cover are the
embeddings of its function field into the field of the geometric point. -/
noncomputable def finiteEtaleGenericHomEquivFunctionFieldAlgHom
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) ≃
      (Y.left.functionField →ₐ[X.functionField] Ω) := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact Equiv.ofBijective
    (finiteEtaleGenericHomFunctionFieldAlgHom (Ω := Ω) Y)
    ⟨finiteEtaleGenericHomFunctionFieldAlgHom_injective Y,
      finiteEtaleGenericHomFunctionFieldAlgHom_surjective Y⟩

/-- An automorphism of a connected finite-etale cover acts on its function
field over the function field of the base. -/
noncomputable def finiteEtaleAutFunctionFieldAlgEquiv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] (σ : Aut Y) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  letI : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let e := finiteEtaleGenericHomEquivFunctionFieldAlgHom
    (Ω := Y.left.functionField) Y
  let g₀ := e.symm (AlgHom.id X.functionField Y.left.functionField)
  exact (algEquivEquivAlgHom X.functionField Y.left.functionField).symm
    (e (g₀ ≫ σ.hom.hom))

private theorem finiteEtaleGenericHomFunctionFieldMap_comp_coverAut
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma)
    (σ : Aut Y) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleGenericHomFunctionFieldMap Y (g ≫ σ.hom.hom) =
      (finiteEtaleGenericHomFunctionFieldMap Y g).comp
        (σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange) := by
  intro hIntegral hAlgebra
  let q : Spec (.of Ω) ⟶ Y.left := finiteEtaleGenericHom Y g
  have hq : q (IsLocalRing.closedPoint Ω) = genericPoint Y.left :=
    finiteEtale_genericPoint_of_over_genericExtension Y g
  have h := genericPointFunctionFieldMap_comp
    σ.hom.left σ.hom.left.surjective.denseRange q hq
  change (finiteEtaleGenericHomFunctionFieldMap Y g).comp
      (σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange) =
    finiteEtaleGenericHomFunctionFieldMap Y (g ≫ σ.hom.hom) at h
  exact h.symm

/-- The function-field automorphism defined using generic fibers is the
actual pullback of rational functions along the deck transformation. -/
theorem finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] (σ : Aut Y) :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    (finiteEtaleAutFunctionFieldAlgEquiv Y σ).toRingHom =
      σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange := by
  intro hIntegral hAlgebra
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let e := finiteEtaleGenericHomEquivFunctionFieldAlgHom
    (Ω := Y.left.functionField) Y
  let g₀ := e.symm (AlgHom.id X.functionField Y.left.functionField)
  have heg₀ : e g₀ = AlgHom.id X.functionField Y.left.functionField := e.apply_symm_apply _
  have hdef : (finiteEtaleAutFunctionFieldAlgEquiv Y σ).toAlgHom =
      e (g₀ ≫ σ.hom.hom) :=
    (algEquivEquivAlgHom X.functionField Y.left.functionField).apply_symm_apply _
  have heg₀_apply (w : Y.left.functionField) :
      finiteEtaleGenericHomFunctionFieldMap Y g₀ w = w :=
    DFunLike.congr_fun heg₀ w
  apply RingHom.ext
  intro z
  calc
    finiteEtaleAutFunctionFieldAlgEquiv Y σ z = e (g₀ ≫ σ.hom.hom) z :=
      DFunLike.congr_fun hdef z
    _ = finiteEtaleGenericHomFunctionFieldMap Y (g₀ ≫ σ.hom.hom) z := rfl
    _ = ((finiteEtaleGenericHomFunctionFieldMap Y g₀).comp
        (σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange)) z :=
      DFunLike.congr_fun (finiteEtaleGenericHomFunctionFieldMap_comp_coverAut Y g₀ σ) z
    _ = σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange z := heg₀_apply _

/-- Pulling a generic point through an automorphism of a connected
finite-etale cover composes its function-field embedding with the
function-field automorphism induced by that cover automorphism. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_comp_aut
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma)
    (σ : Aut Y) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    (finiteEtaleGenericHomFunctionFieldAlgHom Y (g ≫ σ.hom.hom)) =
      (finiteEtaleGenericHomFunctionFieldAlgHom Y g).comp
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ).toAlgHom := by
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  have hmap := finiteEtaleGenericHomFunctionFieldMap_comp_coverAut Y g σ
  have hσ := finiteEtaleAutFunctionFieldAlgEquiv_eq_functionFieldMap Y σ
  apply AlgHom.ext
  intro z
  change finiteEtaleGenericHomFunctionFieldMap Y (g ≫ σ.hom.hom) z = _
  rw [hmap]
  change (finiteEtaleGenericHomFunctionFieldMap Y g)
      (σ.hom.left.functionFieldMap σ.hom.left.surjective.denseRange z) =
    (finiteEtaleGenericHomFunctionFieldAlgHom Y g) (finiteEtaleAutFunctionFieldAlgEquiv Y σ z)
  rw [← DFunLike.congr_fun hσ z]
  rfl

/-- The action on function fields is contravariant: multiplication of
cover automorphisms is reversed on the induced field automorphisms. -/
theorem finiteEtaleAutFunctionFieldAlgEquiv_mul_rev
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] (σ τ : Aut Y) :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    finiteEtaleAutFunctionFieldAlgEquiv Y (σ * τ) =
      finiteEtaleAutFunctionFieldAlgEquiv Y τ *
        finiteEtaleAutFunctionFieldAlgEquiv Y σ := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let e := finiteEtaleGenericHomEquivFunctionFieldAlgHom
    (Ω := Y.left.functionField) Y
  let g₀ := e.symm (AlgHom.id X.functionField Y.left.functionField)
  have hdef (ρ : Aut Y) :
      (finiteEtaleAutFunctionFieldAlgEquiv Y ρ).toAlgHom =
        e (g₀ ≫ ρ.hom.hom) := by
    exact (algEquivEquivAlgHom
      X.functionField Y.left.functionField).apply_symm_apply _
  apply AlgEquiv.ext
  intro z
  have hdefz := congrArg
    (fun a : Y.left.functionField →ₐ[X.functionField]
      Y.left.functionField ↦ a z) (hdef (σ * τ))
  have hmorph : g₀ ≫ (σ * τ).hom.hom =
      (g₀ ≫ τ.hom.hom) ≫ σ.hom.hom := by
    rw [CategoryTheory.Aut.Aut_mul_def]
    exact (Category.assoc _ _ _).symm
  have hnat := finiteEtaleGenericHomFunctionFieldAlgHom_comp_aut
    Y (g₀ ≫ τ.hom.hom) σ
  have hnatz := congrArg
    (fun a : Y.left.functionField →ₐ[X.functionField]
      Y.left.functionField ↦ a z) hnat
  have hdefτz := congrArg
    (fun a : Y.left.functionField →ₐ[X.functionField]
      Y.left.functionField ↦
        a (finiteEtaleAutFunctionFieldAlgEquiv Y σ z)) (hdef τ)
  calc
    finiteEtaleAutFunctionFieldAlgEquiv Y (σ * τ) z =
        e (g₀ ≫ (σ * τ).hom.hom) z := hdefz
    _ = e ((g₀ ≫ τ.hom.hom) ≫ σ.hom.hom) z := by rw [hmorph]
    _ = ((finiteEtaleGenericHomFunctionFieldAlgHom Y
          (g₀ ≫ τ.hom.hom)).comp
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ).toAlgHom) z := hnatz
    _ = finiteEtaleGenericHomFunctionFieldAlgHom Y (g₀ ≫ τ.hom.hom)
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ z) := rfl
    _ = finiteEtaleAutFunctionFieldAlgEquiv Y τ
        (finiteEtaleAutFunctionFieldAlgEquiv Y σ z) := hdefτz.symm
    _ = (finiteEtaleAutFunctionFieldAlgEquiv Y τ *
        finiteEtaleAutFunctionFieldAlgEquiv Y σ) z := rfl

theorem finiteEtaleAutFunctionFieldAlgEquiv_injective
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y] :
    Function.Injective (finiteEtaleAutFunctionFieldAlgEquiv Y) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let e := finiteEtaleGenericHomEquivFunctionFieldAlgHom
    (Ω := Y.left.functionField) Y
  let g₀ := e.symm (AlgHom.id X.functionField Y.left.functionField)
  intro σ τ hστ
  have ha : e (g₀ ≫ σ.hom.hom) = e (g₀ ≫ τ.hom.hom) := by
    change
      (algEquivEquivAlgHom X.functionField Y.left.functionField).symm
          (e (g₀ ≫ σ.hom.hom)) =
        (algEquivEquivAlgHom X.functionField Y.left.functionField).symm
          (e (g₀ ≫ τ.hom.hom)) at hστ
    exact (algEquivEquivAlgHom
      X.functionField Y.left.functionField).symm.injective hστ
  have hg : g₀ ≫ σ.hom.hom = g₀ ≫ τ.hom.hom := e.injective ha
  let q₀ : Spec (.of Y.left.functionField) ⟶ Y.left :=
    finiteEtaleGenericHom Y g₀
  have hq₀ : q₀ (IsLocalRing.closedPoint Y.left.functionField) =
      genericPoint Y.left :=
    finiteEtale_genericPoint_of_over_genericExtension Y g₀
  let : IsDominant q₀ := by
    constructor
    rw [DenseRange]
    rw [dense_iff_closure_eq]
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    rw [← (genericPoint_spec Y.left).def]
    apply closure_mono
    rintro _ rfl
    exact ⟨IsLocalRing.closedPoint Y.left.functionField, hq₀⟩
  have hgleft : g₀.left ≫ σ.hom.left = g₀.left ≫ τ.hom.left := by
    exact congrArg (fun r ↦ r.left) hg
  have hqauto : q₀ ≫ σ.hom.left = q₀ ≫ τ.hom.left := by
    change
      ((eqToIso (Over.mk_left
          (X.genericExtensionMorphism Y.left.functionField))).inv ≫ g₀.left) ≫
          σ.hom.left =
        ((eqToIso (Over.mk_left
          (X.genericExtensionMorphism Y.left.functionField))).inv ≫ g₀.left) ≫
          τ.hom.left
    simpa only [Category.assoc] using
      congrArg (fun r ↦
        (eqToIso (Over.mk_left
          (X.genericExtensionMorphism Y.left.functionField))).inv ≫ r) hgleft
  let f : Y.left ⟶ X := Y.hom
  let : IsFiniteEtale f := Y.2
  have hover : σ.hom.left ≫ f = τ.hom.left ≫ f := by
    exact σ.hom.w.trans τ.hom.w.symm
  have hs : σ.hom.left = τ.hom.left :=
    ext_of_isDominant_of_isSeparated f hover q₀ hqauto
  apply Aut.ext
  apply MorphismProperty.Over.Hom.ext
  exact hs

/-- A categorical Galois finite-etale cover induces a Galois extension of
function fields. -/
theorem isGalois_functionField_of_isGalois_finiteEtale
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    IsGalois X.functionField Y.left.functionField := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : Algebra.IsSeparable X.functionField Y.left.functionField :=
    isSeparable_functionField_of_finiteEtale_isConnected Y
  let Ω := AlgebraicClosure X.functionField
  let ξ : Spec (.of Ω) ⟶ X := X.genericExtensionMorphism Ω
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let a : F.obj Y := Classical.choice inferInstance
  let e : F.obj Y ≃
      (Y.left.functionField →ₐ[X.functionField] Ω) :=
    (AlgebraicGeometry.FiniteEtale.fiberObjEquivHom ξ Y).trans
      (finiteEtaleGenericHomEquivFunctionFieldAlgHom (Ω := Ω) Y)
  have hAut : Nat.card (Aut Y) =
      Module.finrank X.functionField Y.left.functionField := calc
    Nat.card (Aut Y) = Nat.card (F.obj Y) :=
      Nat.card_congr (evaluationEquivOfIsGalois F Y a)
    _ = Nat.card
        (Y.left.functionField →ₐ[X.functionField] Ω) :=
      Nat.card_congr e
    _ = Module.finrank X.functionField Y.left.functionField :=
      AlgHom.natCard_of_splits X.functionField Y.left.functionField Ω
        (fun _ ↦ IsAlgClosed.splits _)
  have hle : Nat.card
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) ≤
      Module.finrank X.functionField Y.left.functionField := calc
    Nat.card
        (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) =
        Nat.card
          (Y.left.functionField →ₐ[X.functionField] Y.left.functionField) :=
      Nat.card_congr
        (algEquivEquivAlgHom X.functionField Y.left.functionField)
    _ ≤ Module.finrank X.functionField Y.left.functionField :=
      card_algHom_le_finrank X.functionField Y.left.functionField
        Y.left.functionField
  have hge : Module.finrank X.functionField Y.left.functionField ≤
      Nat.card
        (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) := by
    rw [← hAut]
    exact Nat.card_le_card_of_injective
      (finiteEtaleAutFunctionFieldAlgEquiv Y)
      (finiteEtaleAutFunctionFieldAlgEquiv_injective Y)
  exact IsGalois.of_card_aut_eq_finrank
    X.functionField Y.left.functionField (le_antisymm hle hge)

/-- The field embedding of a specified generic lift reconstructs that same
geometric point, rather than merely a point over the same base. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_spec
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    Spec.map (CommRingCat.ofHom (finiteEtaleGenericHomFunctionFieldAlgHom Y g).toRingHom) ≫
        Y.left.fromSpecStalk (genericPoint Y.left) =
      (eqToIso (Over.mk_left (X.genericExtensionMorphism Ω))).inv ≫ g.left := by
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  let j := finiteEtaleGenericHomFunctionFieldAlgHom Y g
  let : Algebra Y.left.functionField Ω := j.toRingHom.toAlgebra
  change Y.left.genericExtensionMorphism Ω = finiteEtaleGenericHom Y g
  apply genericPointMorphism_eq_of_stalkMap_eq Y.left
    (Y.left.genericExtensionMorphism Ω) (finiteEtaleGenericHom Y g)
    (Y.left.genericExtensionMorphism_apply_closedPoint Ω)
    (finiteEtale_genericPoint_of_over_genericExtension Y g)
  rw [stalkClosedPointTo_genericExtensionMorphism]
  rfl

/-- Reconstructing the prescribed generic lift also preserves its original
map to the base scheme. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_spec_comp
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) [IsConnected Y]
    {Ω : Type u} [Field Ω] [Algebra X.functionField Ω]
    (g : Over.mk (X.genericExtensionMorphism Ω) ⟶ Y.toComma) :
    letI : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
    (Spec.map (CommRingCat.ofHom (finiteEtaleGenericHomFunctionFieldAlgHom Y g).toRingHom) ≫
        Y.left.fromSpecStalk (genericPoint Y.left)) ≫ Y.hom =
      X.genericExtensionMorphism Ω := by
  let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  exact (congrArg (fun q : Spec (.of Ω) ⟶ Y.left => q ≫ Y.hom)
    (finiteEtaleGenericHomFunctionFieldAlgHom_spec Y g)).trans
      (finiteEtaleGenericHom_comp Y g)

end EtaleFundamentalGroups
