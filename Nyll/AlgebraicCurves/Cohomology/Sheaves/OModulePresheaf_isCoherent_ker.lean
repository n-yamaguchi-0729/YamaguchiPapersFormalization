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

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
# OModule Presheaf is Coherent ker
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_ker

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)
variable [IsLocallyNoetherian V]

theorem isCoherent_ker (hF : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (OModulePresheaf.ker φ) := fun U => by
  have := hF U
  have : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  have : _root_.IsNoetherian (Γ(V, U.1)) (F.obj U.1) := isNoetherian_of_isNoetherianRing_of_finite
    _ _
  exact Module.Finite.of_injective ((OModulePresheaf.kerImSES φ).inc.appSections U.1)
    ((OModulePresheaf.kerImSES φ).injective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry
  _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_ker.AlgebraicGeometry
  in
theorem _root_.AlgebraicGeometry.OModulePresheaf.isCoherent_ker {R : Type u} [CommRing R] {V :
  Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsLocallyNoetherian V] {F G : OModulePresheaf π} (φ :
  OModulePresheaf.Hom F G) (hF : F.IsCoherent) : (OModulePresheaf.ker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_ker φ hF
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isCoherent_ker
end ProofImplementation
