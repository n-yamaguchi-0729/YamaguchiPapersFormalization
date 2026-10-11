/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Epimorphisms induced by locally surjective presheaf maps

Sheafification turns a locally surjective morphism of module presheaves into an epimorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_epi_sheafification_map_of_locallySurjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

universe v v' u'

namespace PresheafOfModules
open _root_.PresheafOfModules
open _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_sheafification_map_of_isLocallySurjective {P Q : PresheafOfModules.{v} R₀}
    (ψ : P ⟶ Q) [Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)] :
    Epi ((sheafification.{v} α).map ψ) := by
  apply (SheafOfModules.toSheaf.{v} R).epi_of_epi_map
  change Epi ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ))
  let _ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J AddCommGrpCat.{v}).map ((toPresheaf R₀).map ψ)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ))
    let _ : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P) ≫
          CategoryTheory.sheafifyMap J ((toPresheaf R₀).map ψ)) := by
      rw [← CategoryTheory.toSheafify_naturality]
      infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J ((toPresheaf R₀).obj P)) _
  infer_instance

end PresheafOfModules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

theorem _root_.AlgebraicGeometry.Scheme.Modules.epi_sheafification_map_of_locallySurjective {P Q :
  X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map ψ) := by
  let _ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map ψ) :=
    ⟨fun {U} s x hx => by
      obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
      exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩⟩
  exact PresheafOfModules.epi_sheafification_map_of_isLocallySurjective (𝟙 X.ringCatSheaf.obj) ψ


end AlgebraicGeometry.Scheme.Modules
end Scheme_Modules_epi_sheafification_map_of_locallySurjective
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
