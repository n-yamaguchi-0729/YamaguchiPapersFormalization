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

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Divisor pushforward Along comp
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_comp

open AlgebraicCurve

private noncomputable def valuationSubringEquivOfEq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v v' : Place K F) (h : v = v') : v.toValuationSubring ≃+* v'.toValuationSubring := by
  subst v'
  exact RingEquiv.refl _

private theorem coe_valuationSubringEquivOfEq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v v' : Place K F) (h : v = v') (a : v.toValuationSubring) :
    ((valuationSubringEquivOfEq v v' h a : v'.toValuationSubring) : F) = (a : F) := by
  subst v'
  rfl

private noncomputable def residueFieldEquivOfEq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v v' : Place K F) (h : v = v') : v.ResidueField ≃+* v'.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (valuationSubringEquivOfEq v v' h)

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F'']
    (φ : F →ₐ[K] F') (ψ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hψφ : (ψ.comp
      φ).toRingHom.IsIntegral)
    (D : Divisor K F'') :
    Divisor.pushforwardAlong (ψ.comp φ) hψφ D =
      Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong ψ hψ D) := by
  let iφ : Algebra F F' := algebraAlong φ
  let iψ : Algebra F' F'' := algebraAlong ψ
  let iψφ : Algebra F F'' := algebraAlong (ψ.comp φ)
  have : IsScalarTower K F F' := isScalarTower_along φ
  have : IsScalarTower K F' F'' := isScalarTower_along ψ
  have : IsScalarTower K F F'' := isScalarTower_along (ψ.comp φ)
  have : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  have : Algebra.IsIntegral F' F'' := isIntegral_along ψ hψ
  have : Algebra.IsIntegral F F'' := isIntegral_along (ψ.comp φ) hψφ
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun x => rfl
  change Divisor.pushforward F D = Divisor.pushforward F (Divisor.pushforward F' D)
  have hres : ∀ w : Place K F'', (w.restrict F').restrict F = w.restrict F := fun _ => rfl
  have hdeg : ∀ w : Place K F'', (w.restrict F').inertiaDeg F * w.inertiaDeg F' = w.inertiaDeg F :=
    by
    intro w
    let iFF' : Algebra ((w.restrict F').restrict F).ResidueField
        (w.restrict F').ResidueField :=
      Place.instAlgebraResidueFieldRestrictPushforward (F := F) (w.restrict F')
    let iFF'' : Algebra ((w.restrict F').restrict F).ResidueField w.ResidueField :=
      ((algebraMap (w.restrict F').ResidueField w.ResidueField).comp
        (algebraMap ((w.restrict F').restrict F).ResidueField
          (w.restrict F').ResidueField)).toAlgebra
    have : IsScalarTower ((w.restrict F').restrict F).ResidueField
        (w.restrict F').ResidueField w.ResidueField := by
      exact IsScalarTower.of_algebraMap_eq fun _ => rfl
    unfold Place.inertiaDeg
    calc
      Module.finrank ((w.restrict F').restrict F).ResidueField
          (w.restrict F').ResidueField *
          Module.finrank (w.restrict F').ResidueField w.ResidueField =
          Module.finrank ((w.restrict F').restrict F).ResidueField w.ResidueField :=
        Module.finrank_mul_finrank ((w.restrict F').restrict F).ResidueField
          (w.restrict F').ResidueField w.ResidueField
      _ = Module.finrank (w.restrict F).ResidueField w.ResidueField :=
        Algebra.finrank_eq_of_equiv_equiv
          (residueFieldEquivOfEq _ _ (hres w)) (RingEquiv.refl _) (by
            ext x
            obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
            change Place.restrictResidueMap F w
                (residueFieldEquivOfEq _ _ (hres w) (IsLocalRing.residue _ a)) =
              Place.restrictResidueMap F' w
                (Place.restrictResidueMap F (w.restrict F') (IsLocalRing.residue _ a))
            rw [residueFieldEquivOfEq, IsLocalRing.ResidueField.mapEquiv_apply,
              IsLocalRing.ResidueField.map_residue, Place.restrictResidueMap_residue,
              Place.restrictResidueMap_residue, Place.restrictResidueMap_residue]
            apply congrArg (IsLocalRing.residue w.toValuationSubring)
            apply Subtype.ext
            change algebraMap F F''
                (((valuationSubringEquivOfEq _ _ (hres w)) a :
                  (w.restrict F).toValuationSubring) : F) =
              algebraMap F' F'' (algebraMap F F' (a : F))
            rw [coe_valuationSubringEquivOfEq, ← IsScalarTower.algebraMap_apply])
  induction D using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add w n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, Divisor.pushforward_single, Divisor.pushforward_single,
      Divisor.pushforward_single, hres w, ← hdeg w, Nat.cast_mul]
    congr 1
    ring_nf
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_comp
end ProofImplementation
