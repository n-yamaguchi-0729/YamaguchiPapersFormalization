/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

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
import Nyll.SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalLocalizationAtPrimeIsStandardSmooth

/-!
# Integral closure of source stalks under smooth morphisms

For a smooth morphism to an affine scheme whose global section ring is a domain and
integrally closed, every source stalk has these properties. The proof uses the smooth
algebra on an affine source chart and its prime localization.
-/

section SmoothStalkNormality

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isDomain_and_isIntegrallyClosed_stalk

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem _root_.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk
    {U S : Scheme.{u}} (f : U ⟶ S) [Smooth f]
    [IsAffine S] [IsDomain Γ(S, ⊤)] [IsIntegrallyClosed Γ(S, ⊤)] (y : U) :
    IsDomain (U.presheaf.stalk y) ∧ IsIntegrallyClosed (U.presheaf.stalk y) := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := U) (x := y) (U := ⊤) trivial
  have hle : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  let _ : Algebra Γ(S, ⊤) Γ(U, W) := (f.appLE ⊤ W hle).hom.toAlgebra
  let _ : Algebra.Smooth Γ(S, ⊤) Γ(U, W) := Smooth.smooth_appLE f (isAffineOpen_top S) hW hle
  let _ : Algebra Γ(U, W) (U.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, hyW⟩ : W)
  let _ : IsLocalization.AtPrime (U.presheaf.stalk y) (hW.primeIdealOf ⟨y, hyW⟩).asIdeal :=
    hW.isLocalization_stalk ⟨y, hyW⟩
  exact (open _root_.Algebra.Smooth in
    isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
      Γ(S, ⊤) Γ(U, W)
      (hW.primeIdealOf ⟨y, hyW⟩).asIdeal (U.presheaf.stalk y))
end AlgebraicCurves.Geometry.Schemes.Proofs.Smooth_isDomain_and_isIntegrallyClosed_stalk
end ProofImplementation

end SmoothStalkNormality

section Smooth_isRegularLocalRing_stalk

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

end Smooth_isRegularLocalRing_stalk
