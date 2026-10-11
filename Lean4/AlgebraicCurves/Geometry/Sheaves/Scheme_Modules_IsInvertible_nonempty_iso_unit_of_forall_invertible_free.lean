/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import AlgebraicCurves.Foundations.Algebra.Module_Invertible_of_projective_of_forall_finrank_eq_one
import AlgebraicCurves.Foundations.Algebra.Module_Invertible_of_ringEquiv

/-!
# Scheme Modules Is Invertible nonempty iso unit of forall invertible free
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TensorProduct

namespace LFRAME

variable (R : Type u) [CommRing R]

/-- The affine scheme associated to the base ring. -/
noncomputable abbrev X : Scheme.{u} := Spec (CommRingCat.of R)

/-- The global sections of the associated module presheaf, viewed as an R-module. -/
noncomputable abbrev N₀ (L : (X R).Modules) : ModuleCat.{u} R :=
  (modulesSpecToSheaf (R := CommRingCat.of R) |>.obj L).presheaf.obj (op ⊤)

/-- The whole affine scheme as an affine open. -/
noncomputable def Utop : (X R).affineOpens := ⟨⊤, isAffineOpen_top (X R)⟩

/-- The canonical identification of the base ring with global functions. -/
noncomputable def σ : R ≃+* Γ(X R, ⊤) :=
  (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv

/-- The R-module structure on global sections supplied by the associated presheaf. -/
@[reducible] noncomputable def modR (L : (X R).Modules) : Module R Γ(L, ⊤) :=
  inferInstanceAs (Module R (N₀ R L))

theorem smul_eq (L : (X R).Modules) (r : R) (m : Γ(L, ⊤)) :
    (letI : Module R Γ(L, ⊤) := modR R L; r • m) = (σ R r) • m := rfl

variable (L : (X R).Modules)
  (htriv : ∀ x : X R, ∃ (V : (X R).Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

include htriv in
theorem invertibleTop : Module.Invertible Γ(X R, ⊤) Γ(L, ⊤) := by
  have : Module.Finite Γ(X R, (Utop R).1) Γ(L, (Utop R).1) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial L htriv (Utop R)
  have : Module.Projective Γ(X R, (Utop R).1) Γ(L, (Utop R).1) :=
    AlgebraicGeometry.Scheme.Modules.projective_sections_of_locallyTrivial L htriv (Utop R)
  exact Module.Invertible.of_projective_of_forall_finrank_eq_one (A := Γ(X R, (Utop R).1))
    Γ(L, (Utop R).1)
    (fun K _ _ =>
      AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        L htriv (Utop R) K)
include htriv in
theorem invertibleR : @Module.Invertible R Γ(L, ⊤) _ _ (modR R L) := by
  have := invertibleTop R L htriv
  let : Module R Γ(L, ⊤) := modR R L
  exact Module.Invertible.of_ringEquiv (σ R) Γ(L, ⊤) (fun r m => smul_eq R L r m)
include htriv in
theorem main
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N) :
    Nonempty (L ≅ SheafOfModules.unit (X R).ringCatSheaf) := by
  have hiso : IsIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) L) :=
    AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial (R := CommRingCat.of R)
      L htriv
  let : Module R Γ(L, ⊤) := modR R L
  have hinvR : Module.Invertible R Γ(L, ⊤) := invertibleR R L htriv
  have hfree : Module.Free R Γ(L, ⊤) := hPic Γ(L, ⊤) hinvR
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := R) (M := Γ(L, ⊤))).mp hfree
  let ι : N₀ R L ≅ ModuleCat.of R R := e.toModuleIso
  let i₁ : L ≅ tilde (N₀ R L) := (asIso (Scheme.Modules.fromTildeΓ (R := CommRingCat.of R) L)).symm
  let i₂ : tilde (N₀ R L) ≅ tilde (ModuleCat.of R R) := (tilde.functor (CommRingCat.of R)).mapIso ι
  let i₃ : tilde (ModuleCat.of R R) ≅ SheafOfModules.unit (X R).ringCatSheaf :=
    tildeSelf (R := CommRingCat.of R)
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃⟩

end LFRAME

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_forall_invertible_free
  (R : Type u) [CommRing R]
    (hPic : ∀ (N : Type u) [AddCommGroup N] [Module R N], Module.Invertible R N → Module.Free R N)
    (L : (Spec (CommRingCat.of R)).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of R)).Modules) := by
  obtain ⟨i⟩ := LFRAME.main R L hL.1 hPic
  exact ⟨i ≪≫ eqToIso (Scheme.Modules.tensorUnit_eq (X := Spec (CommRingCat.of R))).symm⟩
end Scheme_Modules_IsInvertible_nonempty_iso_unit_of_forall_invertible_free
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
