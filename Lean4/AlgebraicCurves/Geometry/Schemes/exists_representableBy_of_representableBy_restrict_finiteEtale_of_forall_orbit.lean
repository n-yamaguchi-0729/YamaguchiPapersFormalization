/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import AlgebraicCurves.Geometry.Descent.DescentAction
import AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_finiteEtale_of_forall_orbit

/-!
# exists representable By of representable By restrict finite Etale of forall orbit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

end exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite in
theorem exists_representableBy_of_representableBy_restrict_finiteEtale_of_forall_orbit
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type (u + 1))
    (hG : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G (Presieve.singleton
      ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap R R')))).counit.app T)))
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hX' : ((Over.map (Spec.map (CommRingCat.ofHom (algebraMap R R')))).op ⋙ G).RepresentableBy
      (Over.mk x'))
    (haff : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map
        (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map
          (CommRingCat.ofHom (algebraMap R R')))) r = x →
        (DescentAction.ofRepresentableBy (Spec.map (CommRingCat.ofHom (algebraMap R R'))) G x'
          hX').act r ∈ U) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (_ : G.RepresentableBy (Over.mk f))
      (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X'),
      e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R')
      exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := ⟨by
    change Function.Surjective (PrimeSpectrum.comap (algebraMap R R'))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  obtain ⟨X, f, e, he, hc⟩ :=
    AlgebraicGeometry.DescentAction.effective_of_finiteEtale_of_forall_orbit R R'
    (DescentAction.ofRepresentableBy _ G x' hX') haff
  have hG' : ∀ T : Over (Spec (CommRingCat.of R)), Presieve.IsSheafFor G
      (Presieve.singleton (DescentAction.coverT (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        T)) := fun T => by
    rw [← DescentAction.counit_app_eq_coverT]
    exact hG T
  obtain ⟨rep⟩ := DescentAction.representableBy_of_compatible _ G x' hX' f e he hG' hc
  exact ⟨X, f, rep, e, he⟩
end AlgebraicGeometry
end ProofImplementation
