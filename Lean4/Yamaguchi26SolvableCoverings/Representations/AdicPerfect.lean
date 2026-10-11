/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Commute
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Instances.Matrix

/-!
# 完全な位相群の合同表現は自明

`I` 進位相を持つ可換環 `A` が `I` 進分離的であるとする。
交換子部分群が稠密な位相群 `G` から `GLₙ(A)` への連続表現が `I` を法として
自明なら、表現自体が自明である。

証明は合同核の pro-p 性を仮定せず、行列の差を直接計算する。
`I^r` を法として単位行列となる二つの行列は、`r ≥ 1` のとき `I^(r+1)` を法として
可換である。これは二つの差の積の成分が `I^(2r) ⊆ I^(r+1)` に入るためである。
したがって各段階の剰余表現は交換子部分群を消し、連続性と稠密性により全体を消す。
帰納的に全ての `I` の冪を法として自明となり、分離性から結論が従う。

系2.6では `I` は極大イデアルであり、完備性からこの分離性が得られる。
この補助定理自体には剰余体の有限性・Noether 性・`G` のコンパクト性は不要である。
-/

noncomputable section

open scoped BigOperators commutatorElement

namespace Yamaguchi26SolvableCoverings

private theorem gl_map_quotient_eq_one_iff
    {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Ideal A) (x : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) x = 1 ↔
      ∀ i j : ι, ((x : Matrix ι ι A) - 1) i j ∈ I := by
  let q := RingHom.mapMatrix (m := ι) (Ideal.Quotient.mk I)
  constructor
  · intro hx i j
    have hx' : q (x : Matrix ι ι A) = 1 := congrArg Units.val hx
    have hzero : q ((x : Matrix ι ι A) - 1) = 0 := by
      rw [map_sub, map_one, hx', sub_self]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrFun (congrFun hzero i) j
  · intro hx
    apply Units.ext
    change q (x : Matrix ι ι A) = 1
    apply sub_eq_zero.mp
    rw [← map_one q, ← map_sub]
    apply Matrix.ext
    intro i j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i j)

private theorem matrix_error_product_eq_zero_mod_succ
    {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Ideal A) (r : ℕ) (hr : 1 ≤ r)
    (M N : Matrix ι ι A)
    (hM : ∀ i j, M i j ∈ I ^ r) (hN : ∀ i j, N i j ∈ I ^ r) :
    RingHom.mapMatrix (Ideal.Quotient.mk (I ^ (r + 1))) (M * N) = 0 := by
  apply Matrix.ext
  intro i j
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change ∑ k : ι, M i k * N k j ∈ I ^ (r + 1)
  apply Submodule.sum_mem
  intro k _
  have hprod : M i k * N k j ∈ I ^ r * I ^ r :=
    Ideal.mul_mem_mul (hM i k) (hN k j)
  have hpow : I ^ r * I ^ r ≤ I ^ (r + 1) := by
    rw [← pow_add]
    exact Ideal.pow_le_pow_right (Nat.add_le_add_left hr r)
  exact hpow hprod

/-- Two matrices congruent to the identity modulo `I^r` commute modulo
`I^(r+1)` when `r ≥ 1`; both products of their error matrices vanish there. -/
private theorem gl_reductions_commute_of_congruent_one
    {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (I : Ideal A) (r : ℕ) (hr : 1 ≤ r)
    (x y : Matrix.GeneralLinearGroup ι A)
    (hx : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ r)) x = 1)
    (hy : Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ r)) y = 1) :
    Commute
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ (r + 1))) x)
      (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ (r + 1))) y) := by
  let q := RingHom.mapMatrix (m := ι) (Ideal.Quotient.mk (I ^ (r + 1)))
  have hxy :
      (q (x : Matrix ι ι A) - 1) * (q (y : Matrix ι ι A) - 1) = 0 := by
    have hzero : q (((x : Matrix ι ι A) - 1) * ((y : Matrix ι ι A) - 1)) = 0 :=
      matrix_error_product_eq_zero_mod_succ I r hr _ _
        ((gl_map_quotient_eq_one_iff (I ^ r) x).mp hx)
        ((gl_map_quotient_eq_one_iff (I ^ r) y).mp hy)
    simpa only [map_mul, map_sub, map_one] using hzero
  have hyx :
      (q (y : Matrix ι ι A) - 1) * (q (x : Matrix ι ι A) - 1) = 0 := by
    have hzero : q (((y : Matrix ι ι A) - 1) * ((x : Matrix ι ι A) - 1)) = 0 :=
      matrix_error_product_eq_zero_mod_succ I r hr _ _
        ((gl_map_quotient_eq_one_iff (I ^ r) y).mp hy)
        ((gl_map_quotient_eq_one_iff (I ^ r) x).mp hx)
    simpa only [map_mul, map_sub, map_one] using hzero
  have herr : Commute (q (x : Matrix ι ι A) - 1)
      (q (y : Matrix ι ι A) - 1) := hxy.trans hyx.symm
  have hcomm : Commute (q (x : Matrix ι ι A)) (q (y : Matrix ι ι A)) := by
    simpa only [sub_add_cancel] using
      (herr.add_right (Commute.one_right _)).add_left (Commute.one_left _)
  apply Units.ext
  exact hcomm

-- The quotient topology must be registered as an instance for the continuity lemma.
private theorem continuous_quotient_of_isOpen
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (I : Ideal A) (hI : IsOpen (I : Set A)) :
    letI : TopologicalSpace (A ⧸ I) := ⊥
    Continuous (Ideal.Quotient.mk I) := by
  let : TopologicalSpace (A ⧸ I) := ⊥
  have : DiscreteTopology (A ⧸ I) := discreteTopology_bot _
  rw [continuous_discrete_rng]
  intro y
  rcases Ideal.Quotient.mk_surjective y with ⟨x, hx⟩
  have hpreimage : Ideal.Quotient.mk I ⁻¹' ({y} : Set (A ⧸ I)) =
      (fun z : A => z - x) ⁻¹' (I : Set A) := by
    ext z
    change Ideal.Quotient.mk I z = y ↔ z - x ∈ I
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hx, sub_eq_zero]
  rw [hpreimage]
  exact hI.preimage (continuous_id.sub continuous_const)

private theorem representation_eq_one_of_dense_commutator_of_commuting_image
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (hperfect : (commutator G).topologicalClosure = ⊤)
    (ρ : G →ₜ* H) (hcomm : ∀ x y : G, Commute (ρ x) (ρ y)) :
    ∀ g : G, ρ g = 1 := by
  have hcommutator : commutator G ≤ ρ.toMonoidHom.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact (hcomm x y).commutator_eq
  have hclosed : IsClosed (ρ.toMonoidHom.ker : Set G) :=
    isClosed_eq ρ.continuous_toFun continuous_const
  have htop : (⊤ : Subgroup G) ≤ ρ.toMonoidHom.ker := by
    rw [← hperfect]
    exact (commutator G).topologicalClosure_minimal hcommutator hclosed
  intro g
  exact MonoidHom.mem_ker.mp (htop (Subgroup.mem_top g))

-- The discrete topology in the inductive step is used by instance search.
/-- A continuous representation of a group with dense commutator subgroup
into matrices over a separated adic ring is trivial if its reduction modulo
the defining ideal is trivial. The congruence filtration is proved directly. -/
theorem adic_representation_eq_one_of_dense_commutator
    {G A ι : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Fintype ι] [DecidableEq ι]
    (I : Ideal A) [IsHausdorff I A] (hAdic : IsAdic I)
    (hperfect : (commutator G).topologicalClosure = ⊤)
    (ρ : G →ₜ* Matrix.GeneralLinearGroup ι A)
    (hmod : ∀ g : G, Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) (ρ g) = 1) :
    ∀ g : G, ρ g = 1 := by
  have hpower : ∀ r : ℕ, ∀ g : G,
      Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (I ^ (r + 1))) (ρ g) = 1 := by
    intro r
    induction r with
    | zero =>
        intro g
        have hI1 : I ^ (0 + 1) = I := by
          simp only [Nat.zero_add, Submodule.pow_one]
        rw [hI1]
        exact hmod g
    | succ r ih =>
        let : TopologicalSpace (A ⧸ I ^ ((r + 1) + 1)) := ⊥
        have : DiscreteTopology (A ⧸ I ^ ((r + 1) + 1)) := discreteTopology_bot _
        have hq : Continuous (Ideal.Quotient.mk (I ^ ((r + 1) + 1))) :=
          continuous_quotient_of_isOpen _ ((isAdic_iff.mp hAdic).1 _)
        let reduction : Matrix.GeneralLinearGroup ι A →ₜ*
            Matrix.GeneralLinearGroup ι (A ⧸ I ^ ((r + 1) + 1)) :=
          { toMonoidHom := Matrix.GeneralLinearGroup.map
              (Ideal.Quotient.mk (I ^ ((r + 1) + 1)))
            continuous_toFun := hq.generalLinearGroup_map }
        apply representation_eq_one_of_dense_commutator_of_commuting_image
          hperfect (reduction.comp ρ)
        intro x y
        exact gl_reductions_commute_of_congruent_one I (r + 1)
          (Nat.succ_le_succ (Nat.zero_le r))
          (ρ x) (ρ y) (ih x) (ih y)
  intro g
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply sub_eq_zero.mp
  apply (inferInstance : IsHausdorff I A).haus
  intro r
  apply SModEq.zero.mpr
  have hmem : ((ρ g : Matrix ι ι A) - 1) i j ∈ I ^ r := by
    cases r with
    | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | succ r => exact (gl_map_quotient_eq_one_iff (I ^ (r + 1)) (ρ g)).mp (hpower r g) i j
  have hsmul :
      (((ρ g : Matrix ι ι A) - 1) i j) • (1 : A) ∈
        I ^ r • (⊤ : Submodule A A) :=
    Submodule.smul_mem_smul hmem (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  simpa only [smul_eq_mul, mul_one, Matrix.sub_apply,
    Matrix.GeneralLinearGroup.coe_one] using hsmul

end Yamaguchi26SolvableCoverings
