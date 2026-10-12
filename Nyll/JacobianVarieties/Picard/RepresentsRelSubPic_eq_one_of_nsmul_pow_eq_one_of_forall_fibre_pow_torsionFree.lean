/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Mathlib.Util.WithWeakNamespace

/-!
# Triviality from fibrewise power torsion-freeness
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PowerTorsionFree

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem eq_one_of_nsmul_pow_eq_one_of_forall_fibre_pow_torsionFree
    {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of ℤ))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) c)
    (D : RelativePic0Designation ℤ c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D) (p : ℕ)
    (htors : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ),
      let := (algEquivZeroGroupCut c ε).commGroupObj
        (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
      ∀ ξ : (relSubPicPresheaf c ε (algEquivZeroGroupCut c ε).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))),
        ξ ^ (p ^ k) = 1 → ξ = 1)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase)
    (hx : hD.relativeGroupLaw.nsmul _ (p ^ k) x = hD.relativeGroupLaw.one _) :
    x = hD.relativeGroupLaw.one _ := by
  let := hD.grpObj
  let T : Over (Spec (CommRingCat.of ℤ)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))
  let := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op T)
  have hlaw : hD.relativeGroupLaw = relativeGroupLawOfGrpObj ℤ D.toBase := rfl
  have hpow : ∀ (n : ℕ)
      (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) D.toBase),
      hD.relativeGroupLaw.nsmul _ n y =
        overHomToSchemeHomOver ((schemeHomOverToOverHom y : T ⟶ Over.mk D.toBase) ^ n) := by
    intro n y
    induction n with
    | zero => rw [RelativeGroupLaw.nsmul_zero, pow_zero, hlaw, relativeGroupLawOfGrpObj_one]
    | succ n ih =>
        rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ, hlaw, relativeGroupLawOfGrpObj_mul,
          schemeHomOverToOverHom_overHomToSchemeHomOver]
  let a : T ⟶ Over.mk D.toBase := schemeHomOverToOverHom x
  have hhom : ∀ (n : ℕ) (b : T ⟶ Over.mk D.toBase),
      hD.representableBy.homEquiv (b ^ n) = hD.representableBy.homEquiv b ^ n := by
    intro n b
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact hD.homEquiv_one T
    | succ n ih => rw [pow_succ, pow_succ, hD.homEquiv_mul, ih]
  have h1 : a ^ (p ^ k) = 1 := by
    apply overHomToSchemeHomOver_injective
    rw [← hpow, hx, hlaw, relativeGroupLawOfGrpObj_one]
  have h2 : hD.representableBy.homEquiv a ^ (p ^ k) = 1 := by
    rw [← hhom, h1]; exact hD.homEquiv_one T
  have h3 : hD.representableBy.homEquiv a = 1 := htors K k _ h2
  have h4 : a = 1 := hD.representableBy.homEquiv.injective (h3.trans (hD.homEquiv_one T).symm)
  calc x = overHomToSchemeHomOver a := (overHomToSchemeHomOver_schemeHomOverToOverHom x).symm
    _ = hD.relativeGroupLaw.one _ := by rw [h4, hlaw, relativeGroupLawOfGrpObj_one]
end JacobianVarieties.Picard.Proofs.PowerTorsionFree
end ProofImplementation
