/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology
import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.TensorSections
import AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isFrameOn
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-!
# Scheme Modules Is Invertible nonempty iso tensor Unit of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules

namespace R2P

theorem nonempty_iso_unit_of_isFrameOn_top {X : Scheme.{u}} {N : X.Modules} (s : Γ(N, ⊤))
    (hs : IsFrameOn s ⊤) : Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨θ, hθ, -⟩ := IsFrameOn.existsUnique_ihomEval_eq (isFrameOn_unitSection (X := X) (U := ⊤)
    ⊤) s
  let μ : 𝟙_ X.Modules ⟶ N := ihomGlobalSectionsEquiv (𝟙_ X.Modules) N θ
  have hμ : μ.app ⊤ (unitSection ⊤) = s := by
    rw [ihomGlobalSectionsEquiv_app_apply]
    have e : ((ihom (𝟙_ X.Modules)).obj N).presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op θ
      = θ := by
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _), op_id,
        CategoryTheory.Functor.map_id]; rfl
    rw [e]; exact hθ
  have : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ (fun _ : Unit => (⊤ : X.Opens))
    (by rw [iSup_const]) (fun _ => unitSection ⊤) (fun _ => s)
    (fun _ => isFrameOn_unitSection (X := X) (U := ⊤) ⊤) (fun _ => hs) (fun _ => hμ)
  exact ⟨(asIso μ).symm⟩

end R2P


theorem _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_isLocalRing
    {A : Type u} [CommRing A] [IsLocalRing A] {N : (Spec (CommRingCat.of A)).Modules}
    (hN : Scheme.Modules.IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of A)).Modules) := by
  obtain ⟨U, s, hx, hs⟩ := hN.exists_isFrameOn (IsLocalRing.closedPoint A)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).mp hx
  subst hU
  exact R2P.nonempty_iso_unit_of_isFrameOn_top s hs
end Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
