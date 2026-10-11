/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections

/-!
# The action of a dual section

Evaluating the dual of a module section agrees with the coefficient obtained from the
restricted internal-Hom section and the canonical restriction of the tensor unit.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_ofUnitSection_sectionDual_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace SectionDualFormula

variable {X : Scheme.{u}} {M : X.Modules}

/-- The section of `M` obtained by evaluating a morphism from the tensor unit at its unit
    section. -/
abbrev sVal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M, U) := s.app U (unitSection U)

lemma map_sVal (s : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op (sVal s U) = sVal s V := by
  have h := (NatTrans.naturality_apply s.mapPresheaf i.op (unitSection U)).symm
  rw [map_unitSection] at h
  exact h

lemma sectionDual_app (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) (t : Γ(Scheme.Modules.dual M, U)) :
    (sectionDual s).app U t = ihomEval M (𝟙_ X.Modules) U (sVal s U) t := by
  change (MonoidalClosed.unitIsoSelf (𝟙_ X.Modules)).hom.app U
      (((MonoidalClosed.pre s).app (𝟙_ X.Modules)).app U t) = _
  rw [unitIsoSelf_hom_app, ihomEval_pre_app]

theorem ofUnitSection_sectionDual_app' (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    ofUnitSection U ((sectionDual s).app U t) =
      coeff s U (ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫ (restrictUnitIso' U.ι).hom) := by
  rw [sectionDual_app]
  have e1 := ihomSectionsEquiv_app_apply U t ⊤ (restrictSection s U)
  have e2 := restrictUnitIso_ι_hom_app_apply U ⊤
    ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  change _ = X.presheaf.map (eqToHom U.ι_image_top.symm).op
      ((restrictUnitIso' U.ι).hom.app ⊤
        ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U)))
  rw [e2]
  change ihomEval M (𝟙_ X.Modules) U (sVal s U) t =
    (𝟙_ X.Modules).presheaf.map (eqToHom U.ι_image_top.symm).op
      ((ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U))
  let m : Γ(M, U.ι ''ᵁ ⊤) := restrictSection s U
  let t' : Γ((ihom M).obj (𝟙_ X.Modules), U.ι ''ᵁ ⊤) :=
    ((Scheme.Modules.dual M).presheaf.map (homOfLE (U.ι_image_le ⊤)).op) t
  have e1' : (ihomSectionsEquiv M (𝟙_ X.Modules) U t).app ⊤ (restrictSection s U) =
      ihomEval M (𝟙_ X.Modules) (U.ι ''ᵁ ⊤) m t' := e1
  rw [e1', map_ihomEval]
  congr 1
  · exact (map_sVal s _).symm
  · change t = ((Scheme.Modules.dual M).presheaf.map _ ≫ (Scheme.Modules.dual M).presheaf.map _) t
    rw [← Functor.map_comp, ← op_comp,
      show (eqToHom U.ι_image_top.symm ≫ homOfLE (U.ι_image_le ⊤) : U ⟶ U) = 𝟙 U from
        Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
    rfl

end SectionDualFormula

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.Modules.ofUnitSection_sectionDual_app
    {X : Scheme.{u}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (t : Γ(Scheme.Modules.dual M, U)) :
    Scheme.Modules.ofUnitSection U ((Scheme.Modules.sectionDual s).app U t) =
      Scheme.Modules.coeff s U
        (Scheme.Modules.ihomSectionsEquiv M (𝟙_ X.Modules) U t ≫
          (Scheme.Modules.restrictUnitIso' U.ι).hom) :=
  AlgebraicGeometry.Scheme.Modules.SectionDualFormula.ofUnitSection_sectionDual_app' s U t
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_ofUnitSection_sectionDual_app
end ProofImplementation
