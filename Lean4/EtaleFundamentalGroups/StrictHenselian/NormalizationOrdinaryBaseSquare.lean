/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryGenericGalois
import EtaleFundamentalGroups.StrictHenselian.OriginalUnramifiedSubfield
import EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy
import EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction
import EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint

/-!
# The actual ordinary-henselization map to the original base

The actual A-to-H-to-L coefficient triangle identifies the composite
ordinary generic point with the canonical original fraction point. The
induced fundamental-group map sends every original decomposition element
to the same original ambient Galois image, as checked on geometric points.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory
open AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory

universe u v

private theorem transportedFundamentalGroupHom_eq_fieldSource
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] [IsSepClosed Ω]
    {S T : Scheme.{u}} (f : S ⟶ T) (s : Spec (.of Ω) ⟶ S) (j : Spec (.of F) ⟶ T)
    (hpoint : s ≫ f = ξ F Ω ≫ j) (a : π₁ᵉᵗ(s)) (σ : Gal(Ω/F))
    (ρ : Ω →+* Ω) (hσ : σ.toRingHom = ρ)
    (ha : ∀ (X : FiniteEtale S) (x : (fiber s).obj X),
      (fiberObjEquivHom s X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom s X x).left) :
    continuousConjAut (eqToIso (congrArg fiber hpoint)) (fundamentalGroupHom f s a) =
      fieldSourceAbsoluteGaloisHom F Ω j σ := by
  have hsource (Y : FiniteEtale (Spec (.of F))) (y : (fib F Ω).obj Y) :
      (fiberObjEquivHom (ξ F Ω) Y
        ((suppliedGaloisEquivFundamentalGroup F Ω σ).hom.app Y y)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom (ξ F Ω) Y y).left :=
    (suppliedGaloisEquivFundamentalGroup_point F Ω σ Y y).trans
      (congrArg (fun r : Ω →+* Ω => Spec.map (CommRingCat.ofHom r) ≫
        (fiberObjEquivHom (ξ F Ω) Y y).left) hσ)
  apply Aut.ext
  ext X x
  apply (fiberObjEquivHom (ξ F Ω ≫ j) X).injective
  apply Over.OverMorphism.ext
  exact (point_action_of_eqToIso hpoint (fundamentalGroupHom f s a) ρ
    (fundamentalGroupHom_point_of_point_action f s a ρ ha) X x).trans
      (fundamentalGroupHom_point_of_point_action j (ξ F Ω)
        (suppliedGaloisEquivFundamentalGroup F Ω σ) ρ hsource X x).symm

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The actual ordinary generic point composes to the canonical original
fraction point, by their proved equality on the original base coefficients. -/
theorem normalizationOrdinaryGenericBasePoint :
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    Spec.algebraMap (ordinaryHenselization A) L ≫
        Spec.map (CommRingCat.ofHom (ordinaryHenselizationMap A)) =
      ξ (FractionRing A) L ≫ Spec.algebraMap A (FractionRing A) := by
  intro actualFaithful actualFractionAlgebra actualOrdinaryAlgebra
  have hcoeff : (algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A)) =
      algebraMap A L := (IsScalarTower.algebraMap_eq A (FractionRing A) L).symm
  calc
    _ = Spec.map (CommRingCat.ofHom
        ((ordinaryHenselizationToNormalizationField A K L Q hQ).comp
          (ordinaryHenselizationMap A))) :=
      (Spec.map_comp (CommRingCat.ofHom (ordinaryHenselizationMap A))
        (CommRingCat.ofHom (ordinaryHenselizationToNormalizationField A K L Q hQ))).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap A L)) :=
      congrArg (fun r : A →+* L => Spec.map (CommRingCat.ofHom r))
        (ordinaryHenselizationToNormalizationField_comp_map A K L Q hQ)
    _ = Spec.map (CommRingCat.ofHom
        ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A)))) :=
      congrArg (fun r : A →+* L => Spec.map (CommRingCat.ofHom r)) hcoeff.symm
    _ = ξ (FractionRing A) L ≫ Spec.algebraMap A (FractionRing A) :=
      Spec.map_comp (CommRingCat.ofHom (algebraMap A (FractionRing A)))
        (CommRingCat.ofHom (algebraMap (FractionRing A) L))

/-- The fundamental-group homomorphism of the actual ordinary-henselization
morphism, with its target transported by the proved literal point equality. -/
def normalizationOrdinaryBaseFundamentalGroupHom :
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) →ₜ*
      π₁ᵉᵗ(ξ (FractionRing A) L ≫ Spec.algebraMap A (FractionRing A)) := by
  intro actualFaithful actualFractionAlgebra actualOrdinaryAlgebra
  let f := Spec.map (CommRingCat.ofHom (ordinaryHenselizationMap A))
  let t := eqToIso (congrArg fiber (normalizationOrdinaryGenericBasePoint A K L Q hQ))
  exact (ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
    (fundamentalGroupHom f (Spec.algebraMap (ordinaryHenselization A) L))

variable [IsIntegrallyClosed A]

/-- The actual scheme map carries the ordinary generic image of each original
D element to its canonical original generic image over A. -/
theorem normalizationOrdinaryBaseFundamentalGroupHom_comp_generic :
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
    let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
    let : IsSepClosure (FractionRing A) L := originalFractionField_isSepClosure A K L
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    (normalizationOrdinaryBaseFundamentalGroupHom A K L Q hQ).toMonoidHom.comp
        (normalizationOrdinaryGenericGaloisMap A K L Q hQ) =
      (originalFractionAbsoluteGaloisHom A K L).toMonoidHom.comp
        (normalizationDecompositionInclusion A K L Q) := by
  intro actualFaithful actualBaseAlgebra actualFractionAlgebra actualSepClosure
    actualOrdinaryAlgebra
  apply MonoidHom.ext
  intro d
  let H := ordinaryHenselization A
  let F := FractionRing A
  let f := Spec.map (CommRingCat.ofHom (ordinaryHenselizationMap A))
  let j := Spec.algebraMap A F
  let a := normalizationOrdinaryGenericGaloisMap A K L Q hQ d
  let σ := (originalFractionFieldGaloisEquiv A K L).symm d.val
  have hσ : σ.toRingHom = d.val.toRingHom :=
    (originalFractionFieldGaloisEquiv_toRingHom A K L σ).symm.trans
      (congrArg (fun τ : Gal(L/K) => τ.toRingHom)
        ((originalFractionFieldGaloisEquiv A K L).apply_symm_apply d.val))
  exact transportedFundamentalGroupHom_eq_fieldSource F L f (Spec.algebraMap H L) j
    (normalizationOrdinaryGenericBasePoint A K L Q hQ) a σ d.val.toRingHom hσ
      (normalizationOrdinaryGenericGaloisMap_point A K L Q hQ d)

end EtaleFundamentalGroups.StrictHenselian
