/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_dualNumber_of_reduction.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Util.WithWeakNamespace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero

/-!
# Triviality of an invertible module over dual numbers

A trivial reduction lifts across the square-zero kernel of the dual-number projection.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DualNumberReduction
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible
  (nonempty_iso_unit_of_pullback_squareZero) in
with_weak_namespace _root_.AlgebraicGeometry.RelPicard.Scheme.Modules.IsInvertible
theorem nonempty_iso_unit_of_dualNumber_of_reduction
    (Cr : Type u) [CommRing Cr] (M : (Spec (.of (DualNumber Cr))).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (h0 : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Cr Cr Cr).toRingHom))).obj M ≅
        SheafOfModules.unit.{u} (Spec (.of Cr)).ringCatSheaf)) :
    Nonempty (M ≅ SheafOfModules.unit.{u} (Spec (.of (DualNumber Cr))).ringCatSheaf) := by
  obtain ⟨e0⟩ := h0
  set fst : DualNumber Cr →+* Cr := (TrivSqZeroExt.fstHom Cr Cr Cr).toRingHom with hfst
  let I : Ideal (DualNumber Cr) := RingHom.ker fst
  have hmem : ∀ a : DualNumber Cr, a ∈ I ↔ a.fst = 0 := fun a => Iff.rfl
  have hI : I ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [hmem] at ha hb
    rw [Submodule.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · change a.fst * b.fst = 0
      rw [ha, zero_mul]
    · change a.fst * b.snd + a.snd * b.fst = 0
      rw [ha, hb, zero_mul, mul_zero, zero_add]
  have hsurj : Function.Surjective fst := fun c => ⟨TrivSqZeroExt.inl c, TrivSqZeroExt.fst_inl Cr c⟩
  let q : (DualNumber Cr ⧸ I) ≃+* Cr := RingHom.quotientKerEquivOfSurjective hsurj
  have hq : ∀ x, q (Ideal.Quotient.mk I x) = fst x := fun x => RingHom.kerLift_mk fst x
  have hring : q.symm.toRingHom.comp fst = Ideal.Quotient.mk I :=
    RingHom.ext fun x => (RingEquiv.symm_apply_eq q).mpr (hq x).symm
  have hπ : Spec.map (CommRingCat.ofHom q.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom fst) =
      Spec.map (CommRingCat.ofHom (R := DualNumber Cr) (S := DualNumber Cr ⧸ I)
        (Ideal.Quotient.mk I)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  have h : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj M ≅
      SheafOfModules.unit (Spec (CommRingCat.of (DualNumber Cr ⧸ I))).ringCatSheaf) :=
    ⟨(Scheme.Modules.pullbackCongr hπ.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
      (Scheme.Modules.pullback _).mapIso e0 ≪≫
      Scheme.Modules.pullbackUnitIso _⟩
  exact nonempty_iso_unit_of_pullback_squareZero I hI M hM h
end JacobianVarieties.Picard.Proofs.DualNumberReduction
end ProofImplementation
