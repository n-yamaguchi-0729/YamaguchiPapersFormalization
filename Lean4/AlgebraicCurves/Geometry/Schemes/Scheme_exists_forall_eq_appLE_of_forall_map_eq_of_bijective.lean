/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverOf
import SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_aug_injective
import AlgebraicCurves.Geometry.Schemes.Scheme_OrderedAffineCover_nonempty_of_compactSpace

/-!
# Scheme exists forall eq app LE of forall map eq of bijective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace G5cAffineFamilyConstAux

variable {P : Scheme.{u}}

/-- Restriction of sections along an inclusion of opens. -/
noncomputable abbrev rr {O O' : P.Opens} (h : O ≤ O') : Γ(P, O') →+* Γ(P, O) :=
  (P.presheaf.map (homOfLE h).op).hom

theorem rr_rr {O O' O'' : P.Opens} (h : O ≤ O') (h' : O' ≤ O'') (x : Γ(P, O'')) :
    rr h (rr h' x) = rr (h.trans h') x := by
  change (P.presheaf.map (homOfLE h').op ≫ P.presheaf.map (homOfLE h).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem restrict_inter (𝒲 : P.OrderedAffineCover) {R : Type u} [CommRing R] (π : P ⟶ Spec (.of R))
    [IsSeparated π] {W : P.Opens} (hW : IsAffineOpen W) {b : ℕ} (t : (𝒲.restrict π hW).Idx b) :
    (𝒲.restrict π hW).inter t = 𝒲.inter t ⊓ W := by
  change (⨅ j, 𝒲.U (t.1 j) ⊓ W) = (⨅ j, 𝒲.U (t.1 j)) ⊓ W
  exact le_antisymm (le_inf (iInf_mono fun _ => inf_le_left) ((iInf_le _ 0).trans inf_le_right))
    (le_iInf fun j => inf_le_inf_right _ (iInf_le _ j))

end G5cAffineFamilyConstAux

open G5cAffineFamilyConstAux in
theorem _root_.AlgebraicGeometry.Scheme.exists_forall_eq_appLE_of_forall_map_eq_of_bijective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact fX] [IsSeparated fX]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ fX.appTop).hom)
    (a : ∀ U : X.affineOpens, Γ(X, U.1))
    (ha : ∀ (U U' : X.affineOpens) (h : U'.1 ≤ U.1),
      (X.presheaf.map (homOfLE h).op).hom (a U) = a U') :
    ∃ c : R, ∀ U : X.affineOpens,
      a U = (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  obtain ⟨𝒳⟩ := Scheme.OrderedAffineCover.nonempty_of_compactSpace X
  let := Scheme.OrderedAffineCoverOf.moduleSections fX
  have hKaff : ∀ {b : ℕ} (t : 𝒳.Idx b), IsAffineOpen (𝒳.toCoverOf.inter t) :=
    fun t => Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t
  let A : ∀ {b : ℕ}, 𝒳.Idx b → X.affineOpens := fun t => ⟨𝒳.toCoverOf.inter t, hKaff t⟩
  have hU (U : X.affineOpens) : IsAffineOpen U.1 := U.2
  have hRaff : ∀ (U : X.affineOpens) {b : ℕ} (t : (𝒳.restrict fX (hU U)).Idx b),
      IsAffineOpen ((𝒳.restrict fX (hU U)).inter t) := by
    intro U b t
    rw [restrict_inter]
    exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated fX
      (Scheme.OrderedAffineCover.isAffineOpen_inter fX 𝒳 t) (hU U)
  let A' : ∀ (U : X.affineOpens) {b : ℕ}, (𝒳.restrict fX (hU U)).Idx b → X.affineOpens :=
    fun U {b} t => ⟨(𝒳.restrict fX (hU U)).inter t, hRaff U t⟩
  have hmem : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.ker (𝒳.toCoverOf.d fX 0) := by
    rw [LinearMap.mem_ker]
    funext s
    rw [Scheme.OrderedAffineCoverOf.d_apply, Pi.zero_apply]
    have hj : ∀ j : Fin (0 + 2),
        rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j))) = a (A s) :=
      fun j => ha (A (𝒳.toCoverOf.face s j)) (A s) (𝒳.toCoverOf.inter_le_inter_face s j)
    calc ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          rr (𝒳.toCoverOf.inter_le_inter_face s j) (a (A (𝒳.toCoverOf.face s j)))
        = ∑ j : Fin (0 + 2), ((-1 : ℤ) ^ (j : ℕ)) • a (A s) := Finset.sum_congr rfl fun j _ =>
          by rw [hj]
      _ = 0 := by rw [Fin.sum_univ_two]; simp
  have hrange : (fun t => a (A t) : 𝒳.toCoverOf.cochain 0) ∈ LinearMap.range (𝒳.toCoverOf.aug fX)
    := by
    rw [← AlgebraicGeometry.Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug]
    exact hmem
  obtain ⟨sec, hsec⟩ := hrange
  obtain ⟨c, hc⟩ := hX.2 sec
  refine ⟨c, fun U => ?_⟩
  have hsU : (fX.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)
      = rr (le_top : U.1 ≤ ⊤) sec := by
    rw [← hc]
    rfl
  rw [hsU]
  apply AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective fX (𝒳.restrict fX (hU U))
  funext t
  rw [Scheme.OrderedAffineCoverOf.aug_apply, Scheme.OrderedAffineCoverOf.aug_apply]
  change rr _ (a U) = rr _ (rr _ sec)
  have hle1 : (𝒳.restrict fX (hU U)).inter t ≤ 𝒳.toCoverOf.inter t := by
    rw [restrict_inter]; exact inf_le_left
  have h1 : rr ((𝒳.restrict fX (hU U)).inter_le_base t) (a U) = a (A' U t) := ha U (A' U t) _
  have h2 : rr hle1 (a (A t)) = a (A' U t) := ha (A t) (A' U t) hle1
  have h3 : rr (𝒳.toCoverOf.inter_le_base t) sec = a (A t) := congrFun hsec t
  rw [h1, rr_rr, ← h2, ← h3, rr_rr]
end Scheme_exists_forall_eq_appLE_of_forall_map_eq_of_bijective
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx
attribute [-simp] AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq
