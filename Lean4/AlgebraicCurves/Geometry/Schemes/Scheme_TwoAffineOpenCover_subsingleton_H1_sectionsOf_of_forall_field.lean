/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Finiteness.Nakayama
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Cohomology.Cech.Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial

/-!
# Scheme Two Affine Open Cover subsingleton H1 sections Of of forall field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
namespace H1Fibre
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open TensorProduct

theorem subsingleton_of_forall_maximal {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M]
  [Module A M]
    [Module.Finite A M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], Subsingleton ((A ⧸ m) ⊗[A] M)) : Subsingleton M := by
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  have hann : Module.annihilator A M ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ Module.annihilator A M := htop ▸ Submodule.mem_top
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (by simpa only [one_smul] using Module.mem_annihilator.mp h1 x)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
  have htop : (⊤ : Submodule A M) ≤ m • ⊤ := by
    intro x _
    have : Subsingleton (M ⧸ (m • ⊤ : Submodule A M)) :=
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.toEquiv.subsingleton
    have hx : Submodule.Quotient.mk x = (0 : M ⧸ (m • ⊤ : Submodule A M)) := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (⊤ : Submodule A M)
      Module.Finite.fg_top htop
  have hrann : r ∈ Module.annihilator A M := Module.mem_annihilator.mpr fun x => hr x
    Submodule.mem_top
  have h1 : (1 : A) ∈ m := by
    have := m.sub_mem (hle hrann) hr1
    rwa [sub_sub_cancel] at this
  exact hm.ne_top (m.eq_top_of_isUnit_mem h1 isUnit_one)

theorem main {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π
        (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A
          K))).obj F)).H1) :
    Subsingleton (𝒱.sectionsOf π F).H1 := by
  have := hfin
  refine subsingleton_of_forall_maximal (A := A) _ fun m _ => ?_
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  obtain ⟨⟨e⟩, -, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial 𝒱 π F htriv
      (A ⧸ m)
  have := hfib (A ⧸ m)
  exact e.symm.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1Fibre

theorem
  _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_forall_field
    {A : Type u} [CommRing A] {X : Scheme.{u}} (π : X ⟶ Spec (.of A))
    (𝒱 : X.TwoAffineOpenCover) (F : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj F ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfin : Module.Finite A (𝒱.sectionsOf π F).H1)
    (hfib : ∀ (K : Type u) [Field K] [Algebra A K],
      Subsingleton ((𝒱.pullback π K).sectionsOf (Limits.pullback.snd π
        (Scheme.TwoAffineOpenCover.specMap A K))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap A
          K))).obj F)).H1) :
    Subsingleton (𝒱.sectionsOf π F).H1 :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1Fibre.main π 𝒱 F htriv hfin hfib
end Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_forall_field
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
