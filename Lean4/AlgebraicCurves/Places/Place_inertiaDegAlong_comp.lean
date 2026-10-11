/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Divisors.Correspondences

/-!
# Place inertia Deg Along comp
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_inertiaDegAlong_comp

open IsDedekindDomain AlgebraicCurve

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

theorem _root_.AlgebraicCurve.Place.inertiaDegAlong_comp {K F F' F'' : Type*} [Field K] [Field F]
  [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F'
  →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp
  φ).toRingHom.IsIntegral) (W : Place K F'') : W.inertiaDegAlong (χ.comp φ) hχφ = W.inertiaDegAlong
  χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ := by
  let iχ : Algebra F' F'' := algebraAlong χ
  have := isScalarTower_along χ
  have := isIntegral_along χ hχ
  let iφ : Algebra F F' := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  let iχφ : Algebra F F'' := algebraAlong (χ.comp φ)
  have := isScalarTower_along (χ.comp φ)
  have := isIntegral_along (χ.comp φ) hχφ
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let w : Place K F' := W.restrict F'
  let v : Place K F := w.restrict F
  have hres : v = W.restrict F := rfl
  change W.inertiaDeg F = W.inertiaDeg F' * w.inertiaDeg F
  rw [mul_comm]
  let iFF' : Algebra v.ResidueField w.ResidueField :=
    Place.instAlgebraResidueFieldRestrictPushforward (F := F) w
  let iFF'' : Algebra v.ResidueField W.ResidueField :=
    ((algebraMap w.ResidueField W.ResidueField).comp
      (algebraMap v.ResidueField w.ResidueField)).toAlgebra
  have : IsScalarTower v.ResidueField w.ResidueField W.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold Place.inertiaDeg
  calc
    Module.finrank (W.restrict F).ResidueField W.ResidueField =
        Module.finrank v.ResidueField W.ResidueField :=
      (Algebra.finrank_eq_of_equiv_equiv
        (residueFieldEquivOfEq v (W.restrict F) hres) (RingEquiv.refl _) (by
          ext x
          obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
          change Place.restrictResidueMap F W
              (residueFieldEquivOfEq v (W.restrict F) hres (IsLocalRing.residue _ a)) =
            Place.restrictResidueMap F' W
              (Place.restrictResidueMap F w (IsLocalRing.residue _ a))
          rw [residueFieldEquivOfEq, IsLocalRing.ResidueField.mapEquiv_apply,
            IsLocalRing.ResidueField.map_residue, Place.restrictResidueMap_residue,
            Place.restrictResidueMap_residue, Place.restrictResidueMap_residue]
          apply congrArg (IsLocalRing.residue W.toValuationSubring)
          apply Subtype.ext
          change algebraMap F F''
              (((valuationSubringEquivOfEq v (W.restrict F) hres) a :
                (W.restrict F).toValuationSubring) : F) =
            algebraMap F' F'' (algebraMap F F' (a : F))
          rw [coe_valuationSubringEquivOfEq, ← IsScalarTower.algebraMap_apply])).symm
    _ = Module.finrank v.ResidueField w.ResidueField *
        Module.finrank w.ResidueField W.ResidueField :=
      (Module.finrank_mul_finrank v.ResidueField w.ResidueField W.ResidueField).symm
end AlgebraicCurves.Places.Proofs.Place_inertiaDegAlong_comp
end ProofImplementation
