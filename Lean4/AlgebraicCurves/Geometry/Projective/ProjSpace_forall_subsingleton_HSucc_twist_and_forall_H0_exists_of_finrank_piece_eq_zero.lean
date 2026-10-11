/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import SchemeTheory.ProjectiveSpace.Basic
import SchemeTheory.ProjectiveSpace.Cover
import AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import AlgebraicCurves.Hilbert.Functor.Basic
import AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow

/-!
# Proj Space forall subsingleton HSucc twist and forall H0 exists of finrank piece eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

end ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
end AlgebraicCurves.Geometry.Projective.Proofs

namespace AlgebraicGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MvPolynomial _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

open _root_.AlgebraicCurves.Geometry.Projective.Proofs in
open ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero in
theorem ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
    (n m : ℕ) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k)) (hJ0 : Module.finrank k (piece J m) = 0)
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
      [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin
          (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0))) :
    ∀ d : ℕ, m ≤ d →
      (∀ i : ℕ, Subsingleton
          ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc (ProjSpace.stdCoverPullback ιk) i)) ∧
      (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart
                    ιk i ≤
                    ProjSpace.pullbackChart ιk i)
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                    (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) := by
  classical
  intro d hd
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k with h𝒜
  have : Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m) := by
    refine Module.Finite.of_injective
      (Submodule.inclusion (show MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m ≤
        MvPolynomial.restrictTotalDegree (Fin (n + 1)) k m from fun p hp =>
          (MvPolynomial.mem_restrictTotalDegree _ _ _).2
            (((MvPolynomial.mem_homogeneousSubmodule m p).1 hp).totalDegree_le)))
      (Submodule.inclusion_injective _)
  have hsub : Subsingleton (piece J m) := Module.finrank_zero_iff.1 hJ0
  have hXJ : ∀ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) ^ m ∈ J := by
    intro i
    have hmem : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) ^ m ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m :=
      (MvPolynomial.mem_homogeneousSubmodule m _).2 (MvPolynomial.isHomogeneous_X_pow i m)
    have h0 : (Submodule.Quotient.mk ⟨_, hmem⟩ : piece J m) = 0 := Subsingleton.elim _ _
    have := (Submodule.Quotient.mk_eq_zero _).1 h0
    exact this
  have h10 : ∀ i : Fin (n + 1), (1 : Γ(Zk, ProjSpace.pullbackChart ιk i)) = 0 := by
    intro i
    have h := ((hZ m le_rfl ((MvPolynomial.X i) ^ m) (MvPolynomial.isHomogeneous_X_pow i m)).1 (hXJ
      i)) i
    have e1 : (HomogeneousLocalization.mk
        { deg := m
          num := ⟨(MvPolynomial.X i) ^ m, (MvPolynomial.mem_homogeneousSubmodule m _).mpr
            (MvPolynomial.isHomogeneous_X_pow i m)⟩
          den := ⟨MvPolynomial.X i ^ m, (MvPolynomial.mem_homogeneousSubmodule m _).mpr
            (MvPolynomial.isHomogeneous_X_pow i m)⟩
          den_mem := ⟨m, rfl⟩ } :
        HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          (MvPolynomial.X i)) = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
      exact Localization.mk_self ⟨(MvPolynomial.X i) ^ m, _⟩
    rw [e1, map_one, map_one] at h
    exact h
  have hss : ∀ (U : Zk.Opens) (i : Fin (n + 1)), Subsingleton Γ(Zk, U ⊓ ProjSpace.pullbackChart ιk
    i) := by
    intro U i
    refine subsingleton_iff_zero_eq_one.1 ?_
    have := congrArg (ProjSpace.restrictFun (inf_le_right : U ⊓ ProjSpace.pullbackChart ιk i ≤
      ProjSpace.pullbackChart ιk i)) (h10 i)
    rw [map_one, map_zero] at this
    exact this.symm
  have hto : ∀ (e : ℕ) (U : Zk.Opens), Subsingleton (ProjSpace.twistObj (ιk ≫ ProjSpace.π k n) ιk e
    U) := by
    intro e U
    refine ⟨fun a b => ProjSpace.twistObj.ext (funext fun i => ?_)⟩
    have := hss U i
    exact Subsingleton.elim _ _
  have hobj : ∀ (U : Zk.Opens), Subsingleton ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).obj U)
    :=
    fun U => hto d U
  refine ⟨fun i => ?_, fun c _ => ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    congr 1
    apply Subtype.ext
    funext s
    exact Subsingleton.elim _ _
  · refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, fun s i => ?_⟩
    have := hss ((ProjSpace.stdCoverPullback ιk).inter s) i
    exact Subsingleton.elim _ _
end AlgebraicGeometry
end ProofImplementation
