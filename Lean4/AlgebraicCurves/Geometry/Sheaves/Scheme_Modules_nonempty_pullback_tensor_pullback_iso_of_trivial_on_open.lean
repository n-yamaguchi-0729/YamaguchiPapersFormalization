/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PresheafPullbackMonoidal
import SchemeTheory.Modules.PullbackMonoidal

/-!
# Tensoring with a module trivial on an open

Over the inverse image of an open where a module is trivial, tensoring with its pullback
preserves the restricted pullback of the other module up to isomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

open CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry
    AlgebraicGeometry.Scheme in
theorem
    _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
    {Y T : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) (L : Y.Modules) (N : T.Modules)
    (eN : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V :
        AlgebraicGeometry.Scheme.{u}).Modules)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj
        (L ⊗ (AlgebraicGeometry.Scheme.Modules.pullback q).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj L) := by
  have hfact : (q ⁻¹ᵁ V).ι ≫ q = (q ∣_ V) ≫ V.ι := (morphismRestrict_ι q V).symm
  refine ⟨Scheme.Modules.pullbackTensorObjIso (q ⁻¹ᵁ V).ι L _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp (q ⁻¹ᵁ V).ι q).app N ≪≫
    (Scheme.Modules.pullbackCongr hfact).app N ≪≫
    ((Scheme.Modules.pullbackComp (q ∣_ V) V.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (q ∣_ V)).mapIso eN ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (q ∣_ V)
end Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
