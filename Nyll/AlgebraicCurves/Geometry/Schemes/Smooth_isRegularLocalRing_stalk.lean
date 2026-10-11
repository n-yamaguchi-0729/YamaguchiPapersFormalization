/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.AffineScheme
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.isRegularLocalRing_localization_atPrime_of_isStandardSmooth

/-!
# Smooth is Regular Local Ring stalk
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isRegularLocalRing_stalk

universe u
open CategoryTheory AlgebraicGeometry IsLocalRing

theorem _root_.AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hle, hstd⟩ :=
    Smooth.exists_isStandardSmooth (f := f) x
  have hfxU : f.base x ∈ U := hle hxV
  obtain rfl : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Subsingleton.elim y (f.base x)]; exact hfxU
  let e : k ≃+* Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  let ψ : k →+* Γ(X, V) := (f.appLE ⊤ V hle).hom.comp e.toRingHom
  have hψ : ψ.IsStandardSmooth :=
    RingHom.isStandardSmooth_respectsIso.2 _ e hstd
  let : Algebra k Γ(X, V) := ψ.toAlgebra
  have : Algebra.IsStandardSmooth k Γ(X, V) :=
    (RingHom.isStandardSmooth_algebraMap).mp hψ
  have hreg : IsRegularLocalRing (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) :=
    isRegularLocalRing_localization_atPrime_of_isStandardSmooth k Γ(X, V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxV).hom.toAlgebra
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isRegularLocalRing_stalk
end ProofImplementation
