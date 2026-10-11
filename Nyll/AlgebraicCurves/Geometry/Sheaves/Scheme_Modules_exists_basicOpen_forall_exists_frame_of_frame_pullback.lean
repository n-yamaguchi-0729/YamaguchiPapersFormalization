/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.FrameDescent
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_exists_basicOpen_forall_exists_frame

/-!
# Frames on a basic open from a field-valued fibre

Sections that locally frame the pullback over a residue-field point also locally frame
the original module above a basic open neighbourhood of that point.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback

universe u

section beta_solution
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.exists_basicOpen_forall_exists_frame_of_frame_pullback
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) {ι : Type*} [Finite ι] (m : ι → Γ(M, ⊤))
    (K : Type u) [Field K] [Algebra R K] (𝔭 : PrimeSpectrum R) (h𝔭 : RingHom.ker (algebraMap R K)
      = 𝔭.asIdeal)
    (hgen : ∀ z : ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      ∃ (i : ι) (U' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens),
        z ∈ U' ∧
        ∀ V' : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))).Opens, V' ≤ U'
          →
          Function.Bijective fun g : Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap
            R K))), V') =>
            g • (((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                      M).presheaf.map
                  (homOfLE (le_top : V' ≤ ⊤)).op
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                  (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R
                    K))))).unit.app M).app ⊤) (m i)) :
              Γ((Scheme.Modules.pullback
                    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj
                      M, V'))) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧ ∀ x : X, f x ∈ PrimeSpectrum.basicOpen g →
      ∃ (i : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
        Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (m
          i) : Γ(M, V)) := by
  classical
  apply Scheme.Modules.exists_basicOpen_forall_exists_frame f M m 𝔭
  intro x hx
  have hpt : f x = (Spec.map (CommRingCat.ofHom (algebraMap R K))) (⊥ : PrimeSpectrum K) := by
    rw [hx]
    apply PrimeSpectrum.ext
    change 𝔭.asIdeal = Ideal.comap (algebraMap R K) ⊥
    rw [← RingHom.ker_eq_comap_bot, h𝔭]
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap R K))) x _ hpt
  obtain ⟨i, U', hzU', hU'⟩ := hgen z
  obtain ⟨U, hxU, hU⟩ := Scheme.Modules.exists_frame_of_frame_pullback
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) M hM (m i) z ⟨U',
      hzU', hU'⟩
  exact ⟨i, U, hz ▸ hxU, hU⟩

end beta_solution
end Scheme_Modules_exists_basicOpen_forall_exists_frame_of_frame_pullback
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
