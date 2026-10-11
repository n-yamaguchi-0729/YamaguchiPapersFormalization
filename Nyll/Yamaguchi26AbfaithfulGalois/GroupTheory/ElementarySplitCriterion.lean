/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.ElementaryFaithfulEmbeddingSolution
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.RegularWreathKernel
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaEmbeddingSolutions
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Nyll.ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import Nyll.ProCGroups.FreeProC.Characterization.AbelianKernelOpenSubgroup
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.WreathProducts
import Nyll.ProCGroups.GroupTheory.RegularWreathQuotient
import Nyll.ProCGroups.GroupTheory.SemidirectSubgroups
import Nyll.ProCGroups.FreeProC.Characterization.OpenSubgroupFiniteQuotient
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Split abelian-kernel criteria for Sigma-abelianization-faithfulness

The elementary solver passes to each open subgroup by the induced-kernel
construction. Applied to the actual regular wreath product, it produces
a proper solution with faithful kernel action for each finite quotient.
No restriction is imposed on either whole endpoint of an embedding problem.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.FreeProC.Characterization

universe u

private noncomputable def regularFiberNorm
    {A Q B : Type u} [CommGroup A] [Group Q] [Finite Q] [Group B]
    (J : Subgroup Q) (ρ : J →* B) : (Q → A) →* (B → A) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  refine {
    toFun := fun f b => ∏ j : J, if ρ j = b then f (j : Q) else 1
    map_one' := ?_
    map_mul' := ?_ }
  · funext b
    simp
  · intro f g
    funext b
    simp only [Pi.mul_apply, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : ρ j = b <;> simp [hj]

private theorem regularFiberNorm_equivariant
    {A Q B : Type u} [CommGroup A] [Group Q] [Finite Q] [Group B]
    (J : Subgroup Q) (ρ : J →* B) (j : J) (f : Q → A) :
    regularFiberNorm J ρ
      ((mulAutArrow (G := Q) (A := Q) (M := A)) (j : Q) f) =
      (mulAutArrow (G := B) (A := B) (M := A)) (ρ j) (regularFiberNorm J ρ f) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  funext b
  change (∏ k : J, if ρ k = b then f ((j : Q)⁻¹ * k) else 1) =
    ∏ k : J, if ρ k = (ρ j)⁻¹ * b then f (k : Q) else 1
  let e : J ≃ J := Equiv.mulLeft j⁻¹
  apply Fintype.prod_equiv e
  intro k
  change (if ρ k = b then f ((j : Q)⁻¹ * k) else 1) =
    if ρ (j⁻¹ * k) = (ρ j)⁻¹ * b then f ((j⁻¹ * k : J) : Q) else 1
  have h : ρ k = b ↔ ρ (j⁻¹ * k) = (ρ j)⁻¹ * b := by
    simp only [map_mul, map_inv]
    constructor <;> intro hk
    · rw [hk]
    · apply (mul_left_cancel (a := (ρ j)⁻¹))
      exact hk
  simp only [h]
  rfl

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Proper solvability of all finite split elementary `q`-kernel problems
implies `q`-abelianization-faithfulness, including all open subgroups. -/
theorem isSigmaAbFaithful_singleton_of_elementarySplit_solutions
    (q : ℕ) [Fact q.Prime]
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    IsSigmaAbFaithful {q} G := by
  apply HasFiniteFaithfulAbelianSigmaEmbeddingSolutions.isSigmaAbFaithful
  intro H B hBfinite hBdiscrete π hπ
  have : Finite B := hBfinite
  have : DiscreteTopology B := hBdiscrete
  have hH : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) (H : Subgroup G) :=
    hsolve.openSubgroup (FiniteGroupClass.abelianExponent_subgroupClosed q)
      (FiniteGroupClass.abelianExponent_finiteProductClosed q) H
  exact exists_faithful_primeKernel_embedding_solution q hH B π hπ

/-- For a nonempty set of primes, elementary split solvability at every
member gives both the Sigma condition and each singleton condition. -/
theorem isSigmaAbFaithful_of_elementarySplit_solutions
    {sigma : Set ℕ} (hne : sigma.Nonempty)
    (hprime : ∀ q ∈ sigma, Nat.Prime q)
    (hsolve : ∀ q ∈ sigma, HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    IsSigmaAbFaithful sigma G ∧ ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
  have hsingleton : ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
    intro q hq
    have : Fact q.Prime := ⟨hprime q hq⟩
    exact isSigmaAbFaithful_singleton_of_elementarySplit_solutions q (hsolve q hq)
  obtain ⟨q, hq⟩ := hne
  exact ⟨IsSigmaAbFaithful.mono (Set.singleton_subset_iff.mpr hq) (hsingleton q hq),
    hsingleton⟩

/-- Proper solvability for every finite split abelian Sigma-kernel problem
supplies all the elementary solvers required by the preceding criterion. -/
theorem isSigmaAbFaithful_of_abelianSigmaSplit_solutions
    {sigma : Set ℕ} (hne : sigma.Nonempty)
    (hprime : ∀ q ∈ sigma, Nat.Prime q)
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.sigmaGroup sigma) G) :
    IsSigmaAbFaithful sigma G ∧ ∀ q ∈ sigma, IsSigmaAbFaithful {q} G := by
  apply isSigmaAbFaithful_of_elementarySplit_solutions hne hprime
  intro q hq
  have : Fact q.Prime := ⟨hprime q hq⟩
  intro P hAfin hAdisc hBfin hBdisc hsplit hker hcomm
  exact hsolve P hAfin hAdisc hBfin hBdisc hsplit
    (FiniteGroupClass.sigmaGroup_of_abelianExponent q hq hker) hcomm

/-- The regular wreath-product split embedding problems suffice for
`q`-ab-faithfulness. This is the unnumbered assertion after Proposition 2.1. -/
theorem regular_split_problems_suffice
    {q : ℕ} [Fact q.Prime] (G : ProfiniteGrp.{u})
    (hregular :
      ∀ V : OpenNormalSubgroup G,
        let Q := G ⧸ (V : Subgroup G)
        let W := ProCGroups.WreathProducts.PermutationalWreathProduct
          (ULift.{u} (Multiplicative (ZMod q))) Q Q
        letI : TopologicalSpace W := ⊥
        ∃ θ : G →ₜ* W,
          Function.Surjective θ ∧
            ∀ g : G,
              (SemidirectProduct.rightHom : W →* Q) (θ g) =
                ProCGroups.ProC.OpenNormalSubgroup.quotientProj V g) :
    IsSigmaAbFaithful {q} G := by
  classical
  apply HasFiniteFaithfulAbelianSigmaEmbeddingSolutions.isSigmaAbFaithful
  intro H B hBfinite hBdiscrete π hπ
  have : Finite B := hBfinite
  have : DiscreteTopology B := hBdiscrete
  obtain ⟨V, _hVH, η, ρ, _hη, hρ, hηval, hρη, hpreimage⟩ :=
    exists_finiteQuotient_factor_of_openSubgroup H π hπ
  let Q := G ⧸ (V : Subgroup G)
  let J : Subgroup Q :=
    ((QuotientGroup.mk' (V : Subgroup G)).comp (H : Subgroup G).subtype).range
  let A := ULift.{u} (Multiplicative (ZMod q))
  let W := ProCGroups.WreathProducts.PermutationalWreathProduct A Q Q
  let : TopologicalSpace W := ⊥
  have : DiscreteTopology W := ⟨rfl⟩
  obtain ⟨θ, hθ, hθright⟩ := hregular V
  have hθcoord (g : G) : (θ g).right =
      ProCGroups.ProC.OpenNormalSubgroup.quotientProj V g := hθright g
  let N : Subgroup W := J.comap (SemidirectProduct.rightHom : W →* Q)
  have hθH (h : H) : θ (h : G) ∈ N := by
    change (θ (h : G)).right ∈ J
    rw [hθcoord]
    exact (hpreimage (h : G)).mpr h.property
  let θH : H →ₜ* N :=
    { toMonoidHom :=
        (θ.toMonoidHom.comp (H : Subgroup G).subtype).codRestrict N hθH
      continuous_toFun :=
        (θ.continuous_toFun.comp continuous_subtype_val).subtype_mk hθH }
  have hθHsurj : Function.Surjective θH := by
    intro w
    obtain ⟨x, hx⟩ := hθ (w : W)
    have hxH : x ∈ H := (hpreimage x).mp (by
      rw [← hθcoord x, hx]
      exact w.property)
    exact ⟨⟨x, hxH⟩, Subtype.ext hx⟩
  let φ : Q →* MulAut (Q → A) := mulAutArrow (G := Q) (A := Q) (M := A)
  let eN : N ≃* (Q → A) ⋊[φ.comp J.subtype] J :=
    ProCGroups.semidirectRightPreimageEquiv φ J
  let W_B := ProCGroups.WreathProducts.PermutationalWreathProduct A B B
  let push : (Q → A) ⋊[φ.comp J.subtype] J →* W_B :=
    SemidirectProduct.map (ProCGroups.regularWreathFiberNorm J ρ.toMonoidHom)
      ρ.toMonoidHom (by
        intro j
        apply MonoidHom.ext
        intro f
        exact ProCGroups.regularWreathFiberNorm_equivariant J ρ.toMonoidHom j f)
  have hpush : Function.Surjective push := by
    intro w
    obtain ⟨f, hf⟩ :=
      ProCGroups.regularWreathFiberNorm_surjective J ρ.toMonoidHom hρ w.left
    obtain ⟨j, hj⟩ := hρ w.right
    refine ⟨⟨f, j⟩, ?_⟩
    exact SemidirectProduct.ext hf hj
  let : TopologicalSpace W_B := ⊥
  have : DiscreteTopology W_B := ⟨rfl⟩
  have : Finite W_B := Finite.of_equiv ((B → A) × B)
    (show (B → A) × B ≃ W_B from SemidirectProduct.equivProd.symm)
  let E : TopGrp.{u} := TopGrp.of W_B
  let α : E →ₜ* B :=
    { toMonoidHom := (SemidirectProduct.rightHom : W_B →* B)
      continuous_toFun := continuous_of_discreteTopology }
  have hα : Function.Surjective α := SemidirectProduct.rightHom_surjective
  have hcomm : ∀ a b : α.toMonoidHom.ker, Commute (a : E) (b : E) :=
    regularWreathKernel_commute (A := A) (B := B)
  have hSigma : FiniteGroupClass.sigmaGroup {q} α.toMonoidHom.ker :=
    FiniteGroupClass.sigmaGroup_of_abelianExponent q (Set.mem_singleton q)
      (regularWreathKernel_cyclicZMod_mem_abelianExponent (B := B) q)
  have hfaith : Function.Injective
      (abelianKernelConjugation α.toMonoidHom hα hcomm) :=
    regularWreathKernel_conjugation_injective (A := A) (B := B)
  let ψ : N →ₜ* E :=
    { toMonoidHom := push.comp eN.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨E, inferInstance, inferInstance, α, hα, hcomm, hSigma, hfaith,
    ⟨⟨ψ.comp θH, (hpush.comp eN.surjective).comp hθHsurj, ?_⟩⟩⟩
  apply ContinuousMonoidHom.ext
  intro h
  change ρ ⟨(θ (h : G)).right, hθH h⟩ = π h
  have hcoord : (⟨(θ (h : G)).right, hθH h⟩ : J) = η h := by
    apply Subtype.ext
    exact (hθcoord (h : G)).trans (hηval h).symm
  rw [hcoord]
  exact DFunLike.congr_fun hρη h

end ProCGroups.FiniteStepSolvableQuotients
