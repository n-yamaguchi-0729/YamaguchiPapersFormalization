/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FiberQuotient
import Nyll.EtaleFundamentalGroups.GaloisCovers.PointedQuotientTransport
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime

/-!
# Absolute generic inertia and finite function-field quotients

An automorphism of a fixed separable closure of the function field maps to
the fundamental group at the generic geometric point.  This file compares
its image on every pointed connected finite Galois cover with restriction to
the cover's function field, using the embedding selected by the fiber point.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem fieldGeometricPoint_comp_genericExtensionMorphism
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Omega := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

/-- The canonical identification between the fiber at the composite generic
geometric point and the fiber at the directly constructed generic geometric
point. -/
noncomputable def absoluteGenericFiberIso
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    fiber (ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField) ≅
      fiber (U.genericExtensionMorphism Omega) :=
  (eqToIso (congrArg fiber
    (fieldGeometricPoint_comp_genericExtensionMorphism U Omega).symm)).symm

/-- The homomorphism from the absolute Galois group of the function field to
the fundamental group at its generic geometric point. -/
noncomputable def absoluteGenericGaloisToFundamentalGroup
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega] :
    Gal(Omega/U.functionField) →*
      π₁ᵉᵗ(U.genericExtensionMorphism Omega) :=
  (absoluteGenericFiberIso U Omega).conjAut.toMonoidHom.comp
    ((fundamentalGroupHom
      (U.genericExtensionMorphism U.functionField)
      (ξ U.functionField Omega)).toMonoidHom.comp
        (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
          (IsSepClosure.sep_closed U.functionField)).toMonoidHom)

/-- Evaluation of the absolute generic Galois map as a conjugated
fundamental-group automorphism. -/
theorem absoluteGenericGaloisToFundamentalGroup_apply
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    (sigma : Gal(Omega/U.functionField)) :
    absoluteGenericGaloisToFundamentalGroup U Omega sigma =
      (absoluteGenericFiberIso U Omega).conjAut
    (fundamentalGroupHom
      (U.genericExtensionMorphism U.functionField)
      (ξ U.functionField Omega)
      (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
        (IsSepClosure.sep_closed U.functionField) sigma)) := rfl

/-- The pointed quotient of an absolute generic Galois element is the
corresponding quotient before transport from the composite generic point.
This isolates the remaining comparison from generic lifts to function-field
restriction. -/
theorem finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_transport
    {U : Scheme.{u}} [IsIntegral U] [ConnectedSpace U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    [IsSepClosed Omega]
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W)
    (sigma : Gal(Omega/U.functionField)) :
    finiteEtaleGaloisCoverQuotientMonoidHom
        (U.genericExtensionMorphism Omega) W hW w
        (absoluteGenericGaloisToFundamentalGroup U Omega sigma) =
      finiteEtaleGaloisCoverQuotientMonoidHom
        (ξ U.functionField Omega ≫
          U.genericExtensionMorphism U.functionField)
        W hW ((absoluteGenericFiberIso U Omega).inv.app W w)
        (fundamentalGroupHom
          (U.genericExtensionMorphism U.functionField)
          (ξ U.functionField Omega)
          (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
            (IsSepClosure.sep_closed U.functionField) sigma)) := by
  rw [absoluteGenericGaloisToFundamentalGroup_apply]
  exact (finiteEtaleGaloisCoverQuotientMonoidHom_transport
    (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField)
    (U.genericExtensionMorphism Omega)
    (absoluteGenericFiberIso U Omega) W hW w
    (fundamentalGroupHom
      (U.genericExtensionMorphism U.functionField)
      (ξ U.functionField Omega)
      (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
        (IsSepClosure.sep_closed U.functionField) sigma))).symm

/-- A point of the generic geometric fiber selects the corresponding
embedding of the function field of a connected finite-etale cover. -/
noncomputable def finiteEtaleFiberPointFunctionFieldAlgHom
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    [IsSepClosed Omega]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    W.left.functionField →ₐ[U.functionField] Omega := by
  letI : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  exact finiteEtaleGenericHomFunctionFieldAlgHom W
    (fiberObjEquivHom (U.genericExtensionMorphism Omega) W w)

/-- The algebra structure on the geometric-point field selected by a point
of a connected finite-etale cover.  It is kept explicit because different
fiber points generally select different embeddings. -/
@[reducible] noncomputable def finiteEtaleFiberPointFunctionFieldAlgebra
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    [IsSepClosed Omega]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    Algebra W.left.functionField Omega := by
  letI : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  letI : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  exact (finiteEtaleFiberPointFunctionFieldAlgHom W w).toRingHom.toAlgebra

/-- The point-selected function-field embedding extends the fixed embedding
of the base function field. -/
theorem finiteEtaleFiberPointFunctionFieldIsScalarTower
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    [IsSepClosed Omega]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Omega)).obj W) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    letI : Algebra W.left.functionField Omega :=
      finiteEtaleFiberPointFunctionFieldAlgebra W w
    IsScalarTower U.functionField W.left.functionField Omega := by
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  let j := finiteEtaleFiberPointFunctionFieldAlgHom W w
  let : Algebra W.left.functionField Omega :=
    finiteEtaleFiberPointFunctionFieldAlgebra W w
  apply IsScalarTower.of_algebraMap_eq'
  ext z
  exact (j.commutes z).symm

/-- Precompose a lift of the generic geometric point by an absolute Galois
automorphism, retaining it as a morphism over the base scheme. -/
noncomputable def genericPointLiftPrecomp
    {U : Scheme.{u}} [IsIntegral U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U)
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma)
    (sigma : Gal(Omega/U.functionField)) :
    Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma := by
  let xi := U.genericExtensionMorphism Omega
  let baseIso : (Over.mk xi).left ≅ Spec (.of Omega) :=
    eqToIso (Over.mk_left xi)
  let s : Spec (.of Omega) ⟶ Spec (.of Omega) :=
    Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  have hbase : baseIso.hom ≫ xi = (Over.mk xi).hom := by
    change eqToHom (Over.mk_left xi) ≫ xi = (Over.mk xi).hom
    exact eq_of_heq (eqToHom_comp_heq xi (Over.mk_left xi))
  have hfix : s ≫ xi = xi := by
    dsimp only [s, xi]
    simp only [Scheme.genericExtensionMorphism]
    rw [← Spec.map_comp_assoc]
    have hring :
        CommRingCat.ofHom (algebraMap U.functionField Omega) ≫
            CommRingCat.ofHom sigma.toRingEquiv.toRingHom =
          CommRingCat.ofHom (algebraMap U.functionField Omega) := by
      ext z
      exact sigma.commutes z
    exact congrArg
      (fun q ↦ q ≫ U.fromSpecStalk (genericPoint U))
      (congrArg Spec.map hring)
  let sigmaOver : Over.mk xi ⟶ Over.mk xi := by
    refine Over.homMk (baseIso.hom ≫ s ≫ baseIso.inv) ?_
    rw [← hbase]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hfix]
  exact sigmaOver ≫ g

private noncomputable def genericPointLiftSchemeHom
    {U : Scheme.{u}} [IsIntegral U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U)
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma) :
    Spec (.of Omega) ⟶ W.left :=
  (eqToIso (Over.mk_left (U.genericExtensionMorphism Omega))).inv ≫ g.left

private theorem genericPointLiftSchemeHom_comp
    {U : Scheme.{u}} [IsIntegral U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U)
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma) :
    genericPointLiftSchemeHom W g ≫ W.hom =
      U.genericExtensionMorphism Omega := by
  let baseIso :
      (Over.mk (U.genericExtensionMorphism Omega)).left ≅ Spec (.of Omega) :=
    eqToIso (Over.mk_left (U.genericExtensionMorphism Omega))
  have hbase : baseIso.hom ≫ U.genericExtensionMorphism Omega =
      (Over.mk (U.genericExtensionMorphism Omega)).hom := by
    change eqToHom (Over.mk_left (U.genericExtensionMorphism Omega)) ≫
        U.genericExtensionMorphism Omega =
      (Over.mk (U.genericExtensionMorphism Omega)).hom
    exact eq_of_heq (eqToHom_comp_heq (U.genericExtensionMorphism Omega)
      (Over.mk_left (U.genericExtensionMorphism Omega)))
  calc
    genericPointLiftSchemeHom W g ≫ W.hom =
        baseIso.inv ≫ (g.left ≫ W.hom) := Category.assoc _ _ _
    _ = baseIso.inv ≫
        (Over.mk (U.genericExtensionMorphism Omega)).hom := by
      exact congrArg (fun r ↦ baseIso.inv ≫ r) g.w
    _ = baseIso.inv ≫
        (baseIso.hom ≫ U.genericExtensionMorphism Omega) := by rw [hbase]
    _ = U.genericExtensionMorphism Omega := baseIso.inv_hom_id_assoc _

private theorem genericPointLiftSchemeHom_genericPoint
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U) [IsConnected W]
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    genericPointLiftSchemeHom W g (IsLocalRing.closedPoint Omega) =
      genericPoint W.left := by
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let f : W.left ⟶ U := W.hom
  let : IsFiniteEtale f := W.2
  have hg :
      f (genericPointLiftSchemeHom W g (IsLocalRing.closedPoint Omega)) =
        genericPoint U := by
    change (genericPointLiftSchemeHom W g ≫ W.hom)
        (IsLocalRing.closedPoint Omega) = genericPoint U
    exact (congrArg
      (fun r : Spec (.of Omega) ⟶ U ↦
        r (IsLocalRing.closedPoint Omega))
      (genericPointLiftSchemeHom_comp W g)).trans
        (U.genericExtensionMorphism_apply_closedPoint Omega)
  have hgeneric : f (genericPoint W.left) = genericPoint U :=
    f.map_genericPoint_of_denseRange
      (finiteEtale_hom_denseRange_of_isConnected W)
  symm
  apply (f.isDiscrete_preimage_singleton (genericPoint U)).eq_of_specializes
    (genericPoint_specializes
      (genericPointLiftSchemeHom W g (IsLocalRing.closedPoint Omega)))
  · exact hgeneric
  · exact hg

private theorem genericPointLiftSchemeHom_precomp
    {U : Scheme.{u}} [IsIntegral U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U)
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma)
    (sigma : Gal(Omega/U.functionField)) :
    genericPointLiftSchemeHom W (genericPointLiftPrecomp W g sigma) =
      Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫
        genericPointLiftSchemeHom W g := by
  let xi := U.genericExtensionMorphism Omega
  let baseIso : (Over.mk xi).left ≅ Spec (.of Omega) :=
    eqToIso (Over.mk_left xi)
  let s : Spec (.of Omega) ⟶ Spec (.of Omega) :=
    Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  change baseIso.inv ≫
      ((baseIso.hom ≫ s ≫ baseIso.inv) ≫ g.left) =
    s ≫ (baseIso.inv ≫ g.left)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem stalkClosedPointTo_specMap_algEquiv
    {K Omega : Type u} [Field K] [Field Omega] [Algebra K Omega]
    (sigma : Gal(Omega/K)) :
    let s := Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
    let x : Spec (.of Omega) := IsLocalRing.closedPoint Omega
    let hclosed : s x = x :=
      IsLocalRing.comap_closedPoint sigma.toRingEquiv.toRingHom
    Scheme.stalkClosedPointTo s =
      ((Spec (.of Omega)).presheaf.stalkCongr
          (.of_eq hclosed)).hom ≫
        (stalkClosedPointIso (CommRingCat.of Omega)).hom ≫
          CommRingCat.ofHom sigma.toRingEquiv.toRingHom := by
  let s := Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  let x : Spec (.of Omega) := IsLocalRing.closedPoint Omega
  let hclosed : s x = x :=
    IsLocalRing.comap_closedPoint sigma.toRingEquiv.toRingHom
  dsimp only
  let e := (Spec (.of Omega)).presheaf.stalkCongr (.of_eq hclosed)
  have he :
      (Spec (.of Omega)).presheaf.germ ⊤ (s x) trivial ≫ e.hom =
        (Spec (.of Omega)).presheaf.germ ⊤ x trivial := by
    exact TopCat.Presheaf.germ_stalkSpecializes
      (F := (Spec (.of Omega)).presheaf)
      (U := ⊤) (y := s x) trivial (x := x) (.of_eq hclosed.symm)
  have heinv :
      (Spec (.of Omega)).presheaf.germ ⊤ x trivial ≫ e.inv =
        (Spec (.of Omega)).presheaf.germ ⊤ (s x) trivial := by
    rw [← he, Category.assoc, e.hom_inv_id, Category.comp_id]
  have : IsIso
      ((Spec (.of Omega)).presheaf.germ ⊤ x trivial) := by
    dsimp only [x]
    rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (.of Omega)]
    infer_instance
  apply (cancel_epi
    ((Spec (.of Omega)).presheaf.germ ⊤ x trivial ≫ e.inv)).1
  calc
    ((Spec (.of Omega)).presheaf.germ ⊤ x trivial ≫ e.inv) ≫
          Scheme.stalkClosedPointTo s =
        (Spec (.of Omega)).presheaf.germ ⊤ (s x) trivial ≫
          Scheme.stalkClosedPointTo s := by rw [heinv]
    _ = (Scheme.ΓSpecIso (.of Omega)).hom ≫
          CommRingCat.ofHom sigma.toRingEquiv.toRingHom :=
      Scheme.germ_stalkClosedPointTo_Spec _
    _ = (Spec (.of Omega)).presheaf.germ ⊤ x trivial ≫
          (stalkClosedPointIso (.of Omega)).hom ≫
            CommRingCat.ofHom sigma.toRingEquiv.toRingHom := by
      dsimp only [x]
      have hfac := germ_stalkClosedPointIso_hom (.of Omega)
      exact (congrArg (fun r ↦ r ≫
        CommRingCat.ofHom sigma.toRingEquiv.toRingHom) hfac).symm
    _ = ((Spec (.of Omega)).presheaf.germ ⊤ x trivial ≫ e.inv) ≫
          (e.hom ≫ (stalkClosedPointIso (.of Omega)).hom ≫
            CommRingCat.ofHom sigma.toRingEquiv.toRingHom) := by simp

/-- The function-field embedding associated to a precomposed generic lift is
the original embedding followed by the absolute Galois automorphism. -/
theorem finiteEtaleGenericHomFunctionFieldAlgHom_precomp
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [Algebra U.functionField Omega]
    (W : FiniteEtale U) [IsConnected W]
    (g : Over.mk (U.genericExtensionMorphism Omega) ⟶ W.toComma)
    (sigma : Gal(Omega/U.functionField)) :
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    letI : Algebra U.functionField W.left.functionField :=
      finiteEtaleFunctionFieldAlgebra W
    finiteEtaleGenericHomFunctionFieldAlgHom W
        (genericPointLiftPrecomp W g sigma) =
      sigma.toAlgHom.comp (finiteEtaleGenericHomFunctionFieldAlgHom W g) := by
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let : Algebra U.functionField W.left.functionField :=
    finiteEtaleFunctionFieldAlgebra W
  let q := genericPointLiftSchemeHom W g
  let qSigma := genericPointLiftSchemeHom W
    (genericPointLiftPrecomp W g sigma)
  have hq : q (IsLocalRing.closedPoint Omega) = genericPoint W.left :=
    genericPointLiftSchemeHom_genericPoint W g
  have hqSigma : qSigma (IsLocalRing.closedPoint Omega) =
      genericPoint W.left :=
    genericPointLiftSchemeHom_genericPoint W
      (genericPointLiftPrecomp W g sigma)
  have hqSigmaEq : qSigma =
      Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom) ≫ q :=
    genericPointLiftSchemeHom_precomp W g sigma
  subst qSigma
  let s := Spec.map (CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  let x : Spec (.of Omega) := IsLocalRing.closedPoint Omega
  have hclosed : s x = x :=
    IsLocalRing.comap_closedPoint sigma.toRingEquiv.toRingHom
  change q x = genericPoint W.left at hq
  change (s ≫ q) x = genericPoint W.left at hqSigma
  change q (s x) = genericPoint W.left at hqSigma
  apply AlgHom.ext
  intro z
  change (((W.left.presheaf.stalkCongr (.of_eq hqSigma.symm)).hom ≫
      Scheme.stalkClosedPointTo (s ≫ q)).hom z) =
    sigma (((W.left.presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
      Scheme.stalkClosedPointTo q).hom z)
  rw [Scheme.stalkClosedPointTo_comp]
  rw [stalkClosedPointTo_specMap_algEquiv sigma]
  rw [Scheme.Hom.stalkMap_congr_point_assoc q
    (s x) x hclosed]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  have hstalk := TopCat.Presheaf.stalkSpecializes_comp_assoc W.left.presheaf
    (specializes_of_eq (congrArg q hclosed.symm)) (specializes_of_eq hqSigma)
    (q.stalkMap x ≫ (stalkClosedPointIso (.of Omega)).hom ≫
      CommRingCat.ofHom sigma.toRingEquiv.toRingHom)
  exact (congrArg
    (fun k : W.left.functionField ⟶ CommRingCat.of Omega => k.hom z) hstalk).trans
    (by rfl)


/-- The canonical absolute divisorial inertia source in the geometric
fundamental group.  It is the image of inertia at one fixed prime of the
absolute normalization. -/
noncomputable def absoluteNormalizationPrimeInertiaSource
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    {A : Type u} [CommRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (Q : Ideal (integralClosure A Omega)) :
    Subgroup (π₁ᵉᵗ(U.genericExtensionMorphism Omega)) := by
  letI : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  exact Subgroup.map (absoluteGenericGaloisToFundamentalGroup U Omega)
    (Q.toAddSubgroup.inertia Gal(Omega/U.functionField))

/-- Membership in the canonical source is witnessed by one absolute Galois
inertia element. -/
theorem mem_absoluteNormalizationPrimeInertiaSource_iff
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    {A : Type u} [CommRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (Q : Ideal (integralClosure A Omega))
    (gamma : π₁ᵉᵗ(U.genericExtensionMorphism Omega)) :
    letI : MulSemiringAction Gal(Omega/U.functionField)
        (integralClosure A Omega) :=
      IsIntegralClosure.MulSemiringAction A U.functionField Omega
        (integralClosure A Omega)
    gamma ∈ absoluteNormalizationPrimeInertiaSource Omega Q ↔
      ∃ sigma : Gal(Omega/U.functionField),
        sigma ∈ Q.toAddSubgroup.inertia Gal(Omega/U.functionField) ∧
          absoluteGenericGaloisToFundamentalGroup U Omega sigma = gamma := by
  let : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  change gamma ∈ Subgroup.map
      (absoluteGenericGaloisToFundamentalGroup U Omega)
      (Q.toAddSubgroup.inertia Gal(Omega/U.functionField)) ↔ _
  rfl

/-- The canonical absolute inertia source lies in the range of the absolute
Galois-to-fundamental-group map. -/
theorem absoluteNormalizationPrimeInertiaSource_le_range
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    {A : Type u} [CommRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (Q : Ideal (integralClosure A Omega)) :
    absoluteNormalizationPrimeInertiaSource Omega Q ≤
      (absoluteGenericGaloisToFundamentalGroup U Omega).range := by
  intro gamma hgamma
  let : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  change gamma ∈ Subgroup.map
      (absoluteGenericGaloisToFundamentalGroup U Omega)
      (Q.toAddSubgroup.inertia Gal(Omega/U.functionField)) at hgamma
  rcases hgamma with ⟨sigma, _, rfl⟩
  exact ⟨sigma, rfl⟩

/-- An element of the canonical absolute source has one absolute inertia
witness whose restriction to every supplied finite normal subextension lies
in inertia at the contracted normalization prime. -/
theorem exists_absolute_inertia_restriction_of_mem_source
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    {A : Type u} [CommRing A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    {L : Type u} [Field L]
    [Algebra U.functionField L] [Algebra A L]
    [IsScalarTower A U.functionField L]
    [FiniteDimensional U.functionField L]
    [_root_.IsGalois U.functionField L]
    [Algebra L Omega] [IsScalarTower U.functionField L Omega]
    [IsScalarTower A L Omega]
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime]
    (gamma : π₁ᵉᵗ(U.genericExtensionMorphism Omega))
    (hgamma : gamma ∈ absoluteNormalizationPrimeInertiaSource Omega Q) :
    letI : MulSemiringAction Gal(Omega/U.functionField)
        (integralClosure A Omega) :=
      IsIntegralClosure.MulSemiringAction A U.functionField Omega
        (integralClosure A Omega)
    letI : MulSemiringAction Gal(L/U.functionField)
        (integralClosure A L) :=
      IsIntegralClosure.MulSemiringAction A U.functionField L
        (integralClosure A L)
    ∃ sigma : Gal(Omega/U.functionField),
      sigma ∈ Q.toAddSubgroup.inertia Gal(Omega/U.functionField) ∧
        absoluteGenericGaloisToFundamentalGroup U Omega sigma = gamma ∧
          AlgEquiv.restrictNormalHom
              (F := U.functionField) (K₁ := Omega) L sigma ∈
            (absoluteNormalizationPrimeContraction
              (A := A) (L := L) (Omega := Omega) Q).toAddSubgroup.inertia
                Gal(L/U.functionField) := by
  let : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  let : MulSemiringAction Gal(L/U.functionField)
      (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A U.functionField L
      (integralClosure A L)
  rcases (mem_absoluteNormalizationPrimeInertiaSource_iff
    Omega Q gamma).mp hgamma with ⟨sigma, hsigma, hmap⟩
  refine ⟨sigma, hsigma, hmap, ?_⟩
  apply absoluteNormalizationPrime_inertia_map_le_contraction
    (A := A) (K := U.functionField) (L := L) (Omega := Omega) Q
  exact ⟨sigma, hsigma, rfl⟩

end EtaleFundamentalGroups.Inertia

end
