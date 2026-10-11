/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationAction
import Nyll.EtaleFundamentalGroups.GeometricFiber.ExtendedFiberGaloisAction

/-!
# Point actions under the canonical specialization conjugation

The explicit natural fiber comparison transports the actual generic point
action to the actual residue point action. Equality of geometric-point maps
also preserves the literal point-action formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Transport along equality of geometric points preserves a literal point action. -/
theorem point_action_of_eqToIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {s t : Spec (.of Ω) ⟶ S} (h : s = t)
    (a : π₁ᵉᵗ(s)) (ρ : Ω →+* Ω)
    (ha : ∀ (X : FiniteEtale S) (x : (fiber s).obj X),
      (fiberObjEquivHom s X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom s X x).left)
    (X : FiniteEtale S) (x : (fiber t).obj X) :
    (fiberObjEquivHom t X
      ((continuousConjAut (eqToIso (congrArg fiber h)) a).hom.app X x)).left =
      Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom t X x).left := by
  subst t
  exact ha X x

variable (H R L : Type u) [CommRing H] [CommRing R]
  [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  [IsSepClosed L] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Conjugation by the actual specialization identifies the two actual point actions. -/
theorem henselianSpecializationFundamentalGroupEquiv_point
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (a : π₁ᵉᵗ(Spec.algebraMap H L))
    (ha : ∀ (X : FiniteEtale (Spec (.of H))) (x : (fiber (Spec.algebraMap H L)).obj X),
      (fiberObjEquivHom (Spec.algebraMap H L) X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (fiberObjEquivHom (Spec.algebraMap H L) X x).left)
    (X : FiniteEtale (Spec (.of H)))
    (x : (fiber (Spec.algebraMap H (IsLocalRing.ResidueField R))).obj X) :
    (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
      ((henselianSpecializationFundamentalGroupEquiv H R L a).hom.app X x)).left =
      Spec.map (CommRingCat.ofHom (SchemeTheory.residueAlgEquiv H R τ).toRingHom) ≫
        (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X x).left := by
  let t := henselianSpecializationFiberIso H R L
  let y := t.inv.app X x
  have hy : t.hom.app X y = x := FintypeCat.inv_hom_id_apply (t.app X) x
  have hay : a.hom.app X y = (fiberObjEquivHom (Spec.algebraMap H L) X).symm
      (mapPointHom H L σ X (fiberObjEquivHom (Spec.algebraMap H L) X y)) := by
    apply (fiberObjEquivHom (Spec.algebraMap H L) X).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    exact ha X y
  change (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
    (t.hom.app X (a.hom.app X y))).left = _
  calc
    _ = (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
        (t.hom.app X ((fiberObjEquivHom (Spec.algebraMap H L) X).symm
          (mapPointHom H L σ X (fiberObjEquivHom (Spec.algebraMap H L) X y))))).left :=
      congrArg (fun z => (fiberObjEquivHom
        (Spec.algebraMap H (IsLocalRing.ResidueField R)) X (t.hom.app X z)).left) hay
    _ = Spec.map (CommRingCat.ofHom (SchemeTheory.residueAlgEquiv H R τ).toRingHom) ≫
        (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
          (t.hom.app X y)).left :=
      congrArg (fun z => z.left) (henselianSpecializationFiberIso_equivariant H R L τ σ hσ X y)
    _ = _ := congrArg (fun z =>
      Spec.map (CommRingCat.ofHom (SchemeTheory.residueAlgEquiv H R τ).toRingHom) ≫
        (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X z).left) hy

end AlgebraicGeometry.FiniteEtale
