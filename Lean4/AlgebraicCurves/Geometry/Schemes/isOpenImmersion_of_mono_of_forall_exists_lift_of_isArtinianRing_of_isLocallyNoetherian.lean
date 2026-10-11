/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import AlgebraicCurves.Geometry.Schemes.isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing

/-!
# is Open Immersion of mono of forall exists lift of is Artinian Ring of is Locally
Noetherian
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

end isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing in
theorem isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocallyNoetherian
    {X M : Scheme.{u}} [IsLocallyNoetherian X] (ϖ : M ⟶ X) [LocallyOfFinitePresentation ϖ] [Mono ϖ]
    (h : ∀ (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
      [CommRing T] [Nontrivial T] (p : T' →+* T), Function.Surjective p → RingHom.ker p *
        maximalIdeal T' = ⊥ →
      ∀ (s : Spec (CommRingCat.of T') ⟶ X) (m : Spec (CommRingCat.of T) ⟶ M),
        m ≫ ϖ = Spec.map (CommRingCat.ofHom p) ≫ s →
        ∃ m' : Spec (CommRingCat.of T') ⟶ M, m' ≫ ϖ = s ∧ Spec.map (CommRingCat.ofHom p) ≫ m' = m) :
    IsOpenImmersion ϖ := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) (fun U : X.affineOpens => (U
    : X.Opens))
    (iSup_affineOpens_eq_top X)
  intro U
  have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  let e : (↑(U : X.Opens) : Scheme.{u}) ≅ Spec Γ(X, (U : X.Opens)) := U.2.isoSpec
  have : Mono (ϖ ∣_ (U : X.Opens)) :=
    mono_of_mono_fac (morphismRestrict_ι ϖ (U : X.Opens))
  have : Mono (ϖ ∣_ (U : X.Opens) ≫ e.hom) := mono_comp _ _
  have : LocallyOfFinitePresentation (ϖ ∣_ (U : X.Opens) ≫ e.hom) := inferInstance
  have key : IsOpenImmersion (ϖ ∣_ (U : X.Opens) ≫ e.hom) := by
    refine isOpenImmersion_of_mono_of_forall_exists_lift_of_isArtinianRing_of_isLocalRing
      (ϖ ∣_ (U : X.Opens) ≫ e.hom) ?_
    intro T' T _ _ _ _ _ p hp hsmall s m hm
    obtain ⟨m₁, hm₁, hm₂⟩ := h T' T p hp hsmall (s ≫ e.inv ≫ (U : X.Opens).ι) (m ≫ (ϖ ⁻¹ᵁ (U :
      X.Opens)).ι) (by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, ← Category.assoc]
      have : m ≫ ϖ ∣_ (U : X.Opens) = (Spec.map (CommRingCat.ofHom p) ≫ s) ≫ e.inv := by
        rw [← hm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [this, Category.assoc, Category.assoc])
    have hrange : Set.range m₁.base ⊆ Set.range (ϖ ⁻¹ᵁ (U : X.Opens)).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      change ϖ.base (m₁.base t) ∈ (U : X.Opens)
      have ht : ϖ.base (m₁.base t) = (U : X.Opens).ι.base (e.inv.base (s.base t)) := by
        have := congrArg (fun φ => φ.base t) hm₁
        simpa using this
      rw [ht]
      exact (e.inv.base (s.base t)).2
    refine ⟨IsOpenImmersion.lift (ϖ ⁻¹ᵁ (U : X.Opens)).ι m₁ hrange, ?_, ?_⟩
    · have : Mono (e.inv ≫ (U : X.Opens).ι) := mono_comp _ _
      apply (cancel_mono (e.inv ≫ (U : X.Opens).ι)).1
      rw [Category.assoc, Category.assoc, e.hom_inv_id_assoc, morphismRestrict_ι, ← Category.assoc,
        IsOpenImmersion.lift_fac, hm₁]
    · apply (cancel_mono (ϖ ⁻¹ᵁ (U : X.Opens)).ι).1
      rw [Category.assoc, IsOpenImmersion.lift_fac, hm₂]
  exact IsOpenImmersion.of_comp (ϖ ∣_ (U : X.Opens)) e.hom
end AlgebraicGeometry
end ProofImplementation
