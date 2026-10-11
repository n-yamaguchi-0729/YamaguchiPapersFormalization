/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationSourceIso
import EtaleFundamentalGroups.Inertia.AffineNormalizationGeometricPoint
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The actual affine coordinate action of a normalized cover

A morphism to an affine base supplies the algebra structure on global
sections. The deck automorphism of those sections is obtained from the
actual scheme automorphism. Naturality of isoSpec then compares its
normalization action with the geometric normalization action.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R : Type u) [CommRing R] {A : Scheme.{u}}

/-- The base algebra on global sections, constructed from the actual map. -/
@[instance_reducible] def affineMorphismAlgebra (f : A ⟶ Spec (.of R)) : Algebra R Γ(A, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.toAlgebra

/-- An actual automorphism over the affine base gives the coordinate-ring
algebra automorphism through its pullback on global sections. -/
def affineMorphismAlgEquiv (f : A ⟶ Spec (.of R)) (sigma : A ≅ A)
    (hsigma : sigma.hom ≫ f = f) :
    let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
    Γ(A, ⊤) ≃ₐ[R] Γ(A, ⊤) := by
  intro hAlgebra
  let e := (Scheme.Γ.mapIso sigma.op).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  have h : f.appTop ≫ sigma.hom.appTop = f.appTop := by
    rw [← Scheme.Hom.comp_appTop, hsigma]
  have h' := congrArg
    (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k) h
  exact ConcreteCategory.congr_hom h' r

theorem affineMorphismAlgEquiv_toRingHom (f : A ⟶ Spec (.of R))
    (sigma : A ≅ A) (hsigma : sigma.hom ≫ f = f) :
    let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
    (affineMorphismAlgEquiv R f sigma hsigma).toRingHom = sigma.hom.appTop.hom := by
  intro hAlgebra
  rfl

variable [IsAffine A]

/-- The affine coordinate structure map is the actual morphism, expressed
through the canonical source isomorphism. -/
theorem isoSpec_affineMorphismAlgebra (f : A ⟶ Spec (.of R)) :
    let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
    A.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(A, ⊤))) = f := by
  intro hAlgebra
  change A.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- The relative normalization of an affine source is its actual coordinate
normalization, with the base algebra supplied by its structure morphism. -/
def affineMorphismNormalizationIso (f : A ⟶ Spec (.of R))
    [QuasiCompact f] [QuasiSeparated f] :
    let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
    f.normalization ≅
      (Spec.map (CommRingCat.ofHom (algebraMap R Γ(A, ⊤)))).normalization := by
  intro hAlgebra
  exact normalizationSourceIso f (Spec.map (CommRingCat.ofHom (algebraMap R Γ(A, ⊤))))
    A.isoSpec (isoSpec_affineMorphismAlgebra R f)

/-- Passing from an affine cover to its coordinate ring preserves the exact
normalization-point stabilizer of every actual deck transformation. -/
theorem affineMorphismNormalizationIso_fixes_iff
    (f : A ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (sigma : A ≅ A) (hsigma : sigma.hom ≫ f = f)
    {T : Scheme.{u}} (z : T ⟶ f.normalization) :
    let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
    (z ≫ (affineMorphismNormalizationIso R f).hom) ≫
        affineNormalizationDeck R Γ(A, ⊤) (affineMorphismAlgEquiv R f sigma hsigma) =
      z ≫ (affineMorphismNormalizationIso R f).hom ↔
    z ≫ normalizationEndomorphism f sigma.hom hsigma = z := by
  intro hAlgebra
  let g := Spec.map (CommRingCat.ofHom (algebraMap R Γ(A, ⊤)))
  let tau := Spec.map (CommRingCat.ofHom
    (affineMorphismAlgEquiv R f sigma hsigma).toRingHom)
  have htau : tau ≫ g = g := by
    dsimp only [tau, g]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (affineMorphismAlgEquiv R f sigma hsigma).commutes r
  have hcommute : sigma.hom ≫ A.isoSpec.hom = A.isoSpec.hom ≫ tau := by
    change sigma.hom ≫ A.isoSpec.hom = A.isoSpec.hom ≫ Spec.map sigma.hom.appTop
    exact (Scheme.isoSpec_hom_naturality sigma.hom).symm
  exact normalizationSourceIso_fixes_iff f g A.isoSpec
    (isoSpec_affineMorphismAlgebra R f) z sigma.hom hsigma tau htau hcommute

end EtaleFundamentalGroups.Inertia
