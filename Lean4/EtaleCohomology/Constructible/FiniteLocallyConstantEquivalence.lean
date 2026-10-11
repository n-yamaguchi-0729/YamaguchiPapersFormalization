/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.FiniteEtaleSheaf
import EtaleCohomology.Constructible.FiniteLocallyConstantSet
import EtaleCohomology.Constructible.Representability
import SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Finite étale schemes and finite locally constant sheaves

The represented-sheaf functor gives an equivalence from finite étale schemes
over an arbitrary scheme to the full subcategory of finite locally constant
sheaves on its small étale site. Full faithfulness is the existing Yoneda
comparison. Essential surjectivity uses the actual finite étale representer
constructed by affine effective descent and Zariski gluing.

No finiteness, connectedness, separation, or field hypothesis is imposed on
the base. The inverse functor and its unit and counit come from the proved
full faithfulness and essential surjectivity, without new global instances.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleCohomology

/-- The full subcategory of finite locally constant set sheaves on the small étale site. -/
abbrev EtaleFiniteLocallyConstantSetSheaf (X : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (IsEtaleFiniteLocallyConstantSet (X := X))

/-- The sheaf of sections of a finite étale scheme, with its proved finite local constancy. -/
def finiteEtaleToFiniteLocallyConstantSetSheaf (X : Scheme.{u}) :
    FiniteEtale X ⥤ EtaleFiniteLocallyConstantSetSheaf X :=
  ObjectProperty.lift (IsEtaleFiniteLocallyConstantSet (X := X))
    (finiteEtaleSheaf X) finiteEtaleSheaf_isEtaleFiniteLocallyConstantSet

/-- Finite étale schemes are equivalent to finite locally constant étale set sheaves. -/
def finiteEtaleEquivFiniteLocallyConstantSetSheaf (X : Scheme.{u}) :
    FiniteEtale X ≌ EtaleFiniteLocallyConstantSetSheaf X := by
  let F := finiteEtaleToFiniteLocallyConstantSetSheaf X
  let hF : F.FullyFaithful :=
    { preimage := fun f => (finiteEtaleSheafFullyFaithful X).preimage f.hom
      map_preimage := fun f => ObjectProperty.hom_ext _
        ((finiteEtaleSheafFullyFaithful X).map_preimage f.hom)
      preimage_map := fun f => (finiteEtaleSheafFullyFaithful X).preimage_map f }
  letI : F.IsEquivalence :=
    { faithful := hF.faithful
      full := hF.full
      essSurj := ⟨fun G => by
        obtain ⟨Z, ⟨e⟩⟩ := G.property.exists_finiteEtaleSheaf_iso
        exact ⟨Z, ⟨ObjectProperty.isoMk (IsEtaleFiniteLocallyConstantSet (X := X)) e⟩⟩⟩ }
  exact F.asEquivalence

end EtaleCohomology
