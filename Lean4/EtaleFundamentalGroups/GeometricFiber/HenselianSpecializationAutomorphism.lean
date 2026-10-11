/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# Automorphism comparison under actual henselian specialization

The entire comparison of the generic and residue point actions is performed
over abstract rings and fields. Callers supply their proved ambient and
native residue ring-map computations and their actual point-action laws.
The resulting equality is between the actual fiber automorphisms.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H R L : Type u) [CommRing H] [CommRing R]
  [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  [IsSepClosed L] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Equality of the proved literal point actions identifies the actual
specialized fiber automorphism with the given residue fiber automorphism. -/
theorem henselianSpecializationFundamentalGroupEquiv_eq_of_point_actions
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hcompat : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (ρ : L →+* L) (hσ : σ.toRingHom = ρ)
    (η : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField R)
    (hτ : (SchemeTheory.residueAlgEquiv H R τ).toRingHom = η)
    (a : π₁ᵉᵗ(Spec.algebraMap H L))
    (b : π₁ᵉᵗ(Spec.algebraMap H (IsLocalRing.ResidueField R)))
    (ha : ∀ (X : FiniteEtale (Spec (.of H))) (x : (fiber (Spec.algebraMap H L)).obj X),
      (fiberObjEquivHom (Spec.algebraMap H L) X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫
          (fiberObjEquivHom (Spec.algebraMap H L) X x).left)
    (hb : ∀ (X : FiniteEtale (Spec (.of H)))
      (x : (fiber (Spec.algebraMap H (IsLocalRing.ResidueField R))).obj X),
      (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
        (b.hom.app X x)).left = Spec.map (CommRingCat.ofHom η) ≫
          (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X x).left) :
    henselianSpecializationFundamentalGroupEquiv H R L a = b := by
  have ha' (X : FiniteEtale (Spec (.of H))) (x : (fiber (Spec.algebraMap H L)).obj X) :
      (fiberObjEquivHom (Spec.algebraMap H L) X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          (fiberObjEquivHom (Spec.algebraMap H L) X x).left :=
    (ha X x).trans (congrArg (fun r : L →+* L => Spec.map (CommRingCat.ofHom r) ≫
      (fiberObjEquivHom (Spec.algebraMap H L) X x).left) hσ.symm)
  apply Aut.ext
  ext X x
  apply (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X).injective
  apply Over.OverMorphism.ext
  exact (henselianSpecializationFundamentalGroupEquiv_point H R L τ σ hcompat a ha' X x).trans
    ((congrArg (fun r : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField R =>
      Spec.map (CommRingCat.ofHom r) ≫
        (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X x).left) hτ).trans
      (hb X x).symm)

end AlgebraicGeometry.FiniteEtale
