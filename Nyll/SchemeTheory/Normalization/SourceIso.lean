/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Relative normalization under an isomorphism of the original source

A morphism of sources over a fixed base induces an actual morphism of
their relative normalizations by the normalization universal property.
An isomorphism of sources induces an isomorphism of normalizations. Both
the maps from the original sources and the structural maps to the base
are retained.

This transports an explicitly constructed affine model of a generic
cover to the relative normalization of the original scheme-theoretic
cover. The two inverse identities follow from uniqueness in the same
universal property.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X X' S : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]

/-- A morphism of the original sources over their common base induces
a morphism of their relative normalizations. -/
def normalizationSourceMap (p : X ⟶ X') (hp : p ≫ g = f) :
    f.normalization ⟶ g.normalization :=
  f.normalizationDesc (p ≫ g.toNormalization) g.fromNormalization (by
    rw [Category.assoc, toNormalization_fromNormalization]
    exact hp.symm)

/-- The induced map preserves the original map into the normalization. -/
@[reassoc]
theorem toNormalization_normalizationSourceMap (p : X ⟶ X') (hp : p ≫ g = f) :
    f.toNormalization ≫ normalizationSourceMap f g p hp = p ≫ g.toNormalization :=
  f.toNormalization_normalizationDesc _ _ _

/-- The induced map of normalizations is over the original common base. -/
@[reassoc]
theorem normalizationSourceMap_fromNormalization (p : X ⟶ X') (hp : p ≫ g = f) :
    normalizationSourceMap f g p hp ≫ g.fromNormalization = f.fromNormalization :=
  f.normalizationDesc_comp _ _ _

/-- An actual isomorphism of original sources over the base induces an
isomorphism of their relative normalizations. -/
def normalizationSourceIso (e : X ≅ X') (he : e.hom ≫ g = f) :
    f.normalization ≅ g.normalization := by
  have hi : e.inv ≫ f = g := by rw [← he, Iso.inv_hom_id_assoc]
  refine
    { hom := normalizationSourceMap f g e.hom he
      inv := normalizationSourceMap g f e.inv hi
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Scheme.Hom.normalization.hom_ext f _ _ f.fromNormalization
    · rw [Category.comp_id, ← Category.assoc, toNormalization_normalizationSourceMap,
        Category.assoc, toNormalization_normalizationSourceMap,
        ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    · rw [Category.assoc, normalizationSourceMap_fromNormalization,
        normalizationSourceMap_fromNormalization]
    · exact Category.id_comp _
  · apply Scheme.Hom.normalization.hom_ext g _ _ g.fromNormalization
    · rw [Category.comp_id, ← Category.assoc, toNormalization_normalizationSourceMap,
        Category.assoc, toNormalization_normalizationSourceMap,
        ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · rw [Category.assoc, normalizationSourceMap_fromNormalization,
        normalizationSourceMap_fromNormalization]
    · exact Category.id_comp _

/-- The normalization isomorphism preserves its map to the common base. -/
@[reassoc]
theorem normalizationSourceIso_hom_fromNormalization
    (e : X ≅ X') (he : e.hom ≫ g = f) :
    (normalizationSourceIso f g e he).hom ≫ g.fromNormalization = f.fromNormalization :=
  normalizationSourceMap_fromNormalization f g e.hom he

/-- The normalization isomorphism retains the specified original source isomorphism. -/
@[reassoc]
theorem toNormalization_normalizationSourceIso_hom
    (e : X ≅ X') (he : e.hom ≫ g = f) :
    f.toNormalization ≫ (normalizationSourceIso f g e he).hom = e.hom ≫ g.toNormalization :=
  toNormalization_normalizationSourceMap f g e.hom he

end AlgebraicGeometry.Scheme.Hom
