/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_ofInvertible_L_iso_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Opposites
import Mathlib.Topology.Sets.Opens
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic.Ext
import Nyll.AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesIhomSections
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_isFrameOn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top

/-!
Over a field, rigidifying an invertible module preserves its underlying line bundle up to
isomorphism.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RigidificationOverField

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry

open AlgebraicGeometry.RelPicard NeronModelInfra

namespace R2Aux

open AlgebraicGeometry.Scheme.Modules


theorem nonempty_iso_unit_of_isFrameOn_top {X : Scheme.{u}} {N : X.Modules} (s : Γ(N, ⊤))
    (hs : IsFrameOn s ⊤) : Nonempty (N ≅ 𝟙_ X.Modules) := by
  obtain ⟨θ, hθ, -⟩ := IsFrameOn.existsUnique_ihomEval_eq
    (isFrameOn_unitSection (X := X) (U := ⊤) ⊤) s
  let μ : 𝟙_ X.Modules ⟶ N := ihomGlobalSectionsEquiv (𝟙_ X.Modules) N θ
  have hμ : μ.app ⊤ (unitSection ⊤) = s := by
    rw [ihomGlobalSectionsEquiv_app_apply]
    have e : ((ihom (𝟙_ X.Modules)).obj N).presheaf.map
        (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op θ = θ := by
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _),
        op_id, CategoryTheory.Functor.map_id]
      rfl
    rw [e]
    exact hθ
  have : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ (fun _ : Unit => (⊤ : X.Opens))
    (by rw [iSup_const]) (fun _ => unitSection ⊤) (fun _ => s)
    (fun _ => isFrameOn_unitSection (X := X) (U := ⊤) ⊤) (fun _ => hs) (fun _ => hμ)
  exact ⟨(asIso μ).symm⟩


theorem nonempty_iso_unit_of_field {K : Type u} [Field K] {N : (Spec (CommRingCat.of K)).Modules}
    (hN : IsInvertible N) : Nonempty (N ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, s, hx, hs⟩ := hN.exists_isFrameOn (IsLocalRing.closedPoint K)
  have hU : U = ⊤ := by
    ext y
    simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    have : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [this]; exact hx
  subst hU
  exact nonempty_iso_unit_of_isFrameOn_top s hs

end R2Aux

theorem _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_ofInvertible_L_iso_of_field
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {L : (pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L ≅ L) := by
  obtain ⟨r⟩ := R2Aux.nonempty_iso_unit_of_field (hL.pullback (rigSection c t ε))
  let M : RigidifiedLineBundle c ε t := ⟨L, hL, ⟨r⟩⟩
  exact RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M
end JacobianVarieties.Picard.Proofs.RigidificationOverField
end ProofImplementation

attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply
  SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
