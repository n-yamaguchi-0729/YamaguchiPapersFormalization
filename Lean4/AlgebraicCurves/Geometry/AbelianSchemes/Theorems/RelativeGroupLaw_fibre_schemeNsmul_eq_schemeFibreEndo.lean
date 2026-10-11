/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Fibre
import AlgebraicCurves.Geometry.Schemes.SchemeFibreEndo

/-!
# Relative Group Law fibre scheme Nsmul eq scheme Fibre Endo
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

end RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem fibre_nsmul (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (n : ℕ)
    (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).nsmul t' n x = fibrePointOfBase s (G.nsmul _ n (fibrePointToBase s x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nsmul_succ, ih, fibre_mul, fibrePointToBase_ofBase, nsmul_succ]

theorem nsmul_coe_eq_comp_schemeNsmul' (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

end GoodReductionJacobian.RelativeGroupLaw

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) (n : ℕ) :
    (G.fibre s).schemeNsmul n = schemeFibreEndo f (G.schemeNsmul n) (G.schemeNsmul_over n) s := by
  apply pullback.hom_ext
  · rw [schemeFibreEndo_fst]
    change ((G.fibre s).nsmul (RelativeGroupLaw.fibreStr f s) n RelativeGroupLaw.idPoint).1 ≫ _ = _
    rw [GoodReductionJacobian.RelativeGroupLaw.fibre_nsmul,
      RelativeGroupLaw.fibrePointOfBase_coe, pullback.lift_fst,
      GoodReductionJacobian.RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul',
      RelativeGroupLaw.fibrePointToBase_coe]
    simp only [Category.id_comp]
  · rw [schemeFibreEndo_snd]
    exact (G.fibre s).schemeNsmul_over n
end RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
