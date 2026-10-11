/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_epi_iff_locallySurjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.Sheaves.Abelian

/-!
# Epimorphisms and locally surjective module maps

A morphism of module sheaves is an epimorphism precisely when sections locally lift
through its components.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_epi_iff_locallySurjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

universe v v' u'

namespace SheafOfModules
open _root_.SheafOfModules
open _root_.SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem epi_toSheaf_map_of_epi {M N : SheafOfModules.{v} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((toSheaf R).map φ) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)
  let G := SheafOfModules.forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let S := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  let ψ := G.map φ
  have hcounit : IsIso adj.counit :=
    inferInstanceAs (IsIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit)
  let εM : S.obj (G.obj M) ≅ M :=
    @asIso _ _ _ _ (adj.counit.app M) (NatIso.isIso_app_of_isIso adj.counit M)
  let εN : S.obj (G.obj N) ≅ N :=
    @asIso _ _ _ _ (adj.counit.app N) (NatIso.isIso_app_of_isIso adj.counit N)
  have hnat : S.map ψ ≫ εN.hom = εM.hom ≫ φ := adj.counit.naturality φ
  have : Epi (S.map ψ) := by
    have : S.map ψ = (εM.hom ≫ φ) ≫ εN.inv := (Iso.eq_comp_inv εN).2 hnat
    rw [this]; infer_instance
  have h0 : S.map (cokernel.π ψ) = 0 := by
    apply zero_of_epi_comp (S.map ψ)
    rw [← S.map_comp, cokernel.condition]
    exact S.map_zero _ _
  let T := PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}
  have hT : ∀ {P Q : PresheafOfModules.{v} R.obj} (f : P ⟶ Q),
      T.map f = (toSheaf R).map (S.map f) := fun f => rfl
  have h0' : T.map (cokernel.π ψ) = 0 := by
    rw [hT, h0]
    exact Functor.map_zero _ _ _
  have hc := isColimitOfHasCokernelOfPreservesColimit T ψ
  have hTψ : Epi (T.map ψ) := by
    refine Preadditive.epi_of_cancel_zero _ (fun g hg => ?_)
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' hc g hg
    rw [← hd]
    change T.map (cokernel.π ψ) ≫ d = 0
    rw [h0', zero_comp]
  have h2 : T.map ψ ≫ ((toSheaf R).mapIso εN).hom =
      ((toSheaf R).mapIso εM).hom ≫ (toSheaf R).map φ := by
    change (toSheaf R).map (S.map ψ) ≫ (toSheaf R).map εN.hom =
      (toSheaf R).map εM.hom ≫ (toSheaf R).map φ
    rw [← Functor.map_comp, ← Functor.map_comp, hnat]
  have : (toSheaf R).map φ =
      ((toSheaf R).mapIso εM).inv ≫ T.map ψ ≫ ((toSheaf R).mapIso εN).hom :=
    (Iso.eq_inv_comp _).2 h2.symm
  rw [this]
  have : IsIso ((toSheaf R).mapIso εN).hom := ((toSheaf R).mapIso εN).isIso_hom
  have hN : Epi ((toSheaf R).mapIso εN).hom :=
    IsIso.epi_of_iso ((toSheaf R).mapIso εN).hom
  have : IsIso ((toSheaf R).mapIso εM).inv := ((toSheaf R).mapIso εM).isIso_inv
  have hM : Epi ((toSheaf R).mapIso εM).inv :=
    IsIso.epi_of_iso ((toSheaf R).mapIso εM).inv
  have h1 : Epi (T.map ψ ≫ ((toSheaf R).mapIso εN).hom) :=
    @epi_comp _ _ _ _ _ (T.map ψ) hTψ _ hN
  exact @epi_comp _ _ _ _ _ _ hM _ h1

end SheafOfModules

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

theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.epi_iff_locallySurjective {M N : X.Modules} (φ :
  M ⟶ N) :
    Epi φ ↔ ∀ (U : X.Opens) (s : Γ(N, U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ N.presheaf.map (homOfLE i).op s ∈ Set.range (φ.app V) := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have key : Epi φ ↔ Sheaf.IsLocallySurjective (F.map φ) := by
    constructor
    · intro hφ
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ :=
        ⟨fun g h w => (cancel_epi φ).1 w⟩
      have : Epi (F.map φ) :=
        @SheafOfModules.epi_toSheaf_map_of_epi _ _ _ X.ringCatSheaf _ _ M N φ hepi
      exact (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ := F.map φ)).2
          inferInstance
    · intro h
      have : Epi (F.map φ) := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u}) (φ :=
          F.map φ)).1 h
      have hepi : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ M N φ := F.epi_of_epi_map inferInstance
      exact ⟨fun g h w => (@cancel_epi _ _ _ _ _ φ hepi _ _).1 w⟩
  rw [key]
  constructor
  · intro h U s x hx
    obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (F.map φ).hom (U := op U) s x hx
    exact ⟨V, i.le, hxV, t, ht⟩
  · intro h
    refine ⟨fun {U} s x hx => ?_⟩
    obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
    exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩


end AlgebraicGeometry.Scheme.Modules
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_Hom_epi_iff_locallySurjective
end ProofImplementation
