/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Normalization.FiniteNormalSource
import EtaleFundamentalGroups.Normalization.GenericFieldSource
import EtaleFundamentalGroups.Inertia.NormalizationSourceIso

/-! # Actual finite normal models from a specified generic field source -/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {X Y : Scheme.{u}} [IsIntegral Y] [IsNormalIntegral Y]
  (f : Y ⟶ X) [IsFinite f]
  {L : Type u} [Field L] (p : Spec (.of L) ⟶ Y)
  [IsDominant p] [IsPreimmersion p] [QuasiCompact p] [QuasiSeparated p]

omit [IsNormalIntegral Y] [IsFinite f] [QuasiCompact p] [QuasiSeparated p] in
private theorem genericFieldSourceIso_hom_genericComposite :
    (genericFieldSourceIso p).hom ≫
      (Y.genericExtensionMorphism Y.functionField ≫ f) = p ≫ f := by
  have hid : CommRingCat.ofHom (algebraMap Y.functionField Y.functionField) = 𝟙 _ := rfl
  simp only [Scheme.genericExtensionMorphism, hid, Spec.map_id, Category.id_comp]
  rw [← Category.assoc, genericFieldSourceIso_hom_fromSpecStalk]

/-- The normalization in the specified generic field is the actual finite
normal source, compatibly with its original map to the base. -/
def finiteNormalFieldSourceIso : (p ≫ f).normalization ≅ Y :=
  Inertia.normalizationSourceIso (p ≫ f)
      (Y.genericExtensionMorphism Y.functionField ≫ f)
      (genericFieldSourceIso p) (genericFieldSourceIso_hom_genericComposite f p) ≪≫
    Scheme.Hom.finiteNormalGenericIso f

/-- The forward isomorphism commutes with the specified finite morphism. -/
theorem finiteNormalFieldSourceIso_hom_fromNormalization :
    (finiteNormalFieldSourceIso f p).hom ≫ f = (p ≫ f).fromNormalization := by
  let e := Scheme.Hom.finiteNormalGenericIso f
  have he : e.hom ≫ f =
      (Y.genericExtensionMorphism Y.functionField ≫ f).fromNormalization := by
    apply (cancel_epi e.inv).mp
    rw [e.inv_hom_id_assoc]
    exact (Scheme.Hom.finiteNormalGenericIso_inv_fromNormalization f).symm
  unfold finiteNormalFieldSourceIso
  rw [Iso.trans_hom, Category.assoc, he]
  exact Inertia.normalizationSourceIso_hom_fromNormalization _ _ _ _

/-- The inverse isomorphism recovers the specified finite morphism. -/
theorem finiteNormalFieldSourceIso_inv_comp :
    (finiteNormalFieldSourceIso f p).inv ≫ (p ≫ f).fromNormalization = f := by
  rw [← finiteNormalFieldSourceIso_hom_fromNormalization f p]
  exact (finiteNormalFieldSourceIso f p).inv_hom_id_assoc _

end EtaleFundamentalGroups
