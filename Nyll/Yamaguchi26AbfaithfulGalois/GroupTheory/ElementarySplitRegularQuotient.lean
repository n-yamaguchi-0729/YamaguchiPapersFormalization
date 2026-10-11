/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.ElementarySplitCriterion
import Nyll.ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.GroupTheory.SemidirectSubgroups
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags
import Nyll.ProCGroups.Abelian.AbelianModPower

/-!
# Proposition 2.1: finite split embedding problems

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Proposition 2.1.
`TopologicalEmbeddingProblem`, `ProperSolution`, and `IsSplit` model the
paper's embedding-problem terminology. The hypothesis below says that
every finite split problem with elementary abelian `q`-kernel has a
proper solution.

The current proposition states `q`-ab-faithfulness. Its proof also constructs
the equivariant regular-module quotient, which is retained below as an
additional conclusion with the same hypotheses.

The regular module `𝔽_q[H/N]` is represented as functions `H/N → ZMod q`.
The source is the actual quotient `Nᵃᵇ/q`, and the equation below gives
left translation on functions explicitly.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.ProC ProCGroups.Abelian
open ProCGroups.FreeProC.Characterization
open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Proper solvability of all finite split elementary abelian `q`-kernel
embedding problems gives an equivariant quotient onto the regular
module at every open normal layer and implies `q`-ab-faithfulness. -/
theorem elementary_split_regular_quotient_and_faithfulness
    {q : ℕ} [Fact q.Prime] (G : ProfiniteGrp.{u})
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    (∀ H : OpenSubgroup G,
      ∀ N : OpenNormalSubgroup (H : Subgroup G),
        let Q := (H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G))
        ∃ f : abelianModPower (N : Subgroup (H : Subgroup G)) q →ₜ*
            Multiplicative (Q → ZMod q),
          Function.Surjective f ∧
            ∀ (h : (H : Subgroup G))
              (z : abelianModPower (N : Subgroup (H : Subgroup G)) q) (x : Q),
              (Multiplicative.toAdd
                  (f (abelianModPowerMap q
                    (ContinuousMonoidHom.toContinuousMonoidHom
                      (Subgroup.conjNormalContinuousMulEquiv
                        (N : Subgroup (H : Subgroup G)) h)) z))) x =
                (Multiplicative.toAdd (f z))
                  ((QuotientGroup.mk' (N : Subgroup (H : Subgroup G)) h)⁻¹ * x)) ∧
      IsSigmaAbFaithful {q} G := by
  refine ⟨?_, isSigmaAbFaithful_singleton_of_elementarySplit_solutions q hsolve⟩
  intro H N
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let Q := (H : Subgroup G) ⧸ (N : Subgroup (H : Subgroup G))
  let A := ULift.{u} (Multiplicative (ZMod q))
  let W := ProCGroups.WreathProducts.PermutationalWreathProduct A Q Q
  let : TopologicalSpace W := ⊥
  have : DiscreteTopology W := ⟨rfl⟩
  have : Finite W := Finite.of_equiv ((Q → A) × Q)
    (show (Q → A) × Q ≃ W from SemidirectProduct.equivProd.symm)
  let E : TopGrp.{u} := TopGrp.of W
  let B : TopGrp.{u} := TopGrp.of Q
  let α : E →ₜ* B :=
    { toMonoidHom := (SemidirectProduct.rightHom : W →* Q)
      continuous_toFun := continuous_of_discreteTopology }
  let π : (H : Subgroup G) →ₜ* B := ProC.OpenNormalSubgroup.quotientProj N
  let P : TopologicalEmbeddingProblem (H : Subgroup G) :=
    ⟨E, B, α, SemidirectProduct.rightHom_surjective, π,
      ProC.OpenNormalSubgroup.quotientProj_surjective N⟩
  let s : B →ₜ* E :=
    { toMonoidHom := (SemidirectProduct.inr : Q →* W)
      continuous_toFun := continuous_of_discreteTopology }
  have hsplit : P.IsSplit := by
    refine ⟨s, ?_⟩
    apply ContinuousMonoidHom.ext
    intro b
    change (SemidirectProduct.rightHom : W →* Q)
      ((SemidirectProduct.inr : Q →* W) b) = b
    exact SemidirectProduct.rightHom_inr b
  have hker : FiniteGroupClass.abelianExponent q α.toMonoidHom.ker :=
    regularWreathKernel_cyclicZMod_mem_abelianExponent (B := Q) q
  have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E) :=
    regularWreathKernel_commute (A := A) (B := Q)
  have hH : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) (H : Subgroup G) :=
    hsolve.openSubgroup (FiniteGroupClass.abelianExponent_subgroupClosed q)
      (FiniteGroupClass.abelianExponent_finiteProductClosed q) H
  obtain ⟨θ⟩ := hH P inferInstance inferInstance inferInstance inferInstance
    hsplit hker hcomm
  have hθright (h : (H : Subgroup G)) : (θ.val h).right = π h :=
    DFunLike.congr_fun θ.property.2 h
  let K₀ : Subgroup W := α.toMonoidHom.ker
  have hθN (n : (N : Subgroup (H : Subgroup G))) : θ.val (n : (H : Subgroup G)) ∈ K₀ := by
    change (θ.val (n : (H : Subgroup G))).right = 1
    rw [hθright]
    exact ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mpr n.property
  let η₀ : (N : Subgroup (H : Subgroup G)) →ₜ* K₀ :=
    { toMonoidHom :=
        (θ.val.toMonoidHom.comp (N : Subgroup (H : Subgroup G)).subtype).codRestrict
          K₀ hθN
      continuous_toFun :=
        (θ.val.continuous_toFun.comp continuous_subtype_val).subtype_mk hθN }
  have hη₀surj : Function.Surjective η₀ := by
    intro k
    obtain ⟨h, hh⟩ := θ.property.1 (k : W)
    have hn : h ∈ N := by
      apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
      rw [← hθright h, hh]
      exact k.property
    exact ⟨⟨h, hn⟩, Subtype.ext hh⟩
  let e₀ : K₀ ≃* (Q → A) := ProCGroups.semidirectRightKernelEquiv
    (mulAutArrow (G := Q) (A := Q) (M := A))
  let e₁ : (Q → A) ≃* (Q → Multiplicative (ZMod q)) :=
    MulEquiv.piCongrRight (fun _ : Q =>
      (MulEquiv.ulift : A ≃* Multiplicative (ZMod q)))
  let e₂ : (Q → Multiplicative (ZMod q)) ≃* Multiplicative (Q → ZMod q) :=
    (MulEquiv.funMultiplicative Q (ZMod q)).symm
  let e : K₀ ≃* Multiplicative (Q → ZMod q) := (e₀.trans e₁).trans e₂
  let η : (N : Subgroup (H : Subgroup G)) →ₜ* Multiplicative (Q → ZMod q) :=
    { toMonoidHom := e.toMonoidHom.comp η₀.toMonoidHom
      continuous_toFun :=
        (continuous_of_discreteTopology : Continuous (fun k : K₀ => e k)).comp
          η₀.continuous_toFun }
  have hηsurj : Function.Surjective η := e.surjective.comp hη₀surj
  have hηeval (n : (N : Subgroup (H : Subgroup G))) (x : Q) :
      (Multiplicative.toAdd (η n)) x =
        ((θ.val (n : (H : Subgroup G))).left x).down.toAdd := rfl
  have hθconj (h : (H : Subgroup G)) (n : (N : Subgroup (H : Subgroup G))) :
      θ.val (((MulAut.conjNormal h) n) : (H : Subgroup G)) =
        θ.val h * θ.val (n : (H : Subgroup G)) * (θ.val h)⁻¹ := by
    rw [MulAut.conjNormal_apply]
    simp only [map_mul, map_inv]
  have hθinl (n : (N : Subgroup (H : Subgroup G))) :
      θ.val (n : (H : Subgroup G)) =
        (SemidirectProduct.inl (θ.val (n : (H : Subgroup G))).left : W) := by
    apply SemidirectProduct.ext
    · rfl
    · change (θ.val (n : (H : Subgroup G))).right = 1
      exact hθN n
  have hηconj (h : (H : Subgroup G)) (n : (N : Subgroup (H : Subgroup G)))
      (x : Q) :
      (Multiplicative.toAdd (η ((MulAut.conjNormal h) n))) x =
        (Multiplicative.toAdd (η n)) ((π h)⁻¹ * x) := by
    calc
      (Multiplicative.toAdd (η ((MulAut.conjNormal h) n))) x =
          ((θ.val (((MulAut.conjNormal h) n) : (H : Subgroup G))).left x).down.toAdd :=
        hηeval _ x
      _ = ((θ.val (n : (H : Subgroup G))).left ((π h)⁻¹ * x)).down.toAdd := by
        rw [hθconj h n, hθinl n]
        have hw := regularWreath_conj_inl_left_apply
          (w := θ.val h) (f := (θ.val (n : (H : Subgroup G))).left) x
        rw [hθright h] at hw
        exact congrArg (fun a : A => a.down.toAdd) hw
      _ = (Multiplicative.toAdd (η n)) ((π h)⁻¹ * x) :=
        (hηeval n _).symm
  have hpow : ∀ a : Multiplicative (Q → ZMod q), a ^ q = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    funext x
    change q • a.toAdd x = (0 : ZMod q)
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let f : abelianModPower (N : Subgroup (H : Subgroup G)) q →ₜ*
      Multiplicative (Q → ZMod q) := abelianModPowerLift q η hpow
  refine ⟨f, abelianModPowerLift_surjective q η hpow hηsurj, ?_⟩
  intro h z x
  refine Quotient.inductionOn' z (fun a => ?_)
  refine Quotient.inductionOn' a (fun n => ?_)
  change (Multiplicative.toAdd (η ((MulAut.conjNormal h) n))) x =
    (Multiplicative.toAdd (η n)) ((π h)⁻¹ * x)
  exact hηconj h n x

end Yamaguchi26AbfaithfulGalois
