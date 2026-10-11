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

import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
A warning-free compatibility proof for the finrank of a prime-power quotient.

This is the filtration argument formerly bundled with the legacy
`NumberTheory.RamificationInertia.Basic` module. It is kept in a project namespace so
the remaining place trace/norm proofs can use the current split ramification imports.
-/

namespace AlgebraicCurves.Compat.FinrankPrimePow

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable (p : Ideal R) (P : Ideal S)

local notation "f" => algebraMap R S

open Module
open UniqueFactorizationMonoid
open Ideal

attribute [local instance] Ideal.Quotient.field

section FactLeComap

local notation "e" => ramificationIdx' p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
noncomputable instance CompatQuotient.algebraQuotientPowRamificationIdx :
    Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp le_pow_ramificationIdx')
@[simp]
theorem CompatQuotient.algebraMap_quotient_pow_ramificationIdx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk (P ^ e) (f x) := rfl
/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferable.
-/
@[instance_reducible]
def CompatQuotient.algebraQuotientOfRamificationIdxNeZero [hfp : NeZero e] :
    Algebra (R ⧸ p) (S ⧸ P) :=
  Ideal.Quotient.algebraQuotientOfLEComap (le_comap_of_ramificationIdx'_ne_zero hfp.out)

attribute [local instance] CompatQuotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem CompatQuotient.algebraMap_quotient_of_ramificationIdx_neZero
    [NeZero e] (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (f x) := rfl
/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
noncomputable def powQuotSuccInclusion (i : ℕ) :
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1)) →ₗ[R ⧸ p]
    Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i) where
  toFun x := ⟨x, Ideal.map_mono (Ideal.pow_le_pow_right i.le_succ) x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem powQuotSuccInclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion p P i) := by
  rintro ⟨_, _⟩ ⟨_, _⟩ h
  rw [Subtype.ext_iff] at h ⊢; assumption

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotientToQuotientRangePowQuotSucc` for this as a linear map,
and `quotientRangePowQuotSuccInclusionEquiv` for this as a linear equivalence.
-/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) :=
  Quotient.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩)
    fun x y h => by
    rw [Submodule.quotientRel_def] at h ⊢
    simp only [map_mul, LinearMap.mem_range]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul a_mem h)⟩, ?_⟩
    ext
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk,
      Subtype.coe_mk, map_mul, map_sub, mul_sub]

theorem quotientToQuotientRangePowQuotSuccAux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ := by
  apply Quotient.map'_mk''

section
variable [hfp : NeZero (ramificationIdx' p P)]

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
noncomputable def quotientToQuotientRangePowQuotSucc
    {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p]
      (P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i) where
  toFun := quotientToQuotientRangePowQuotSuccAux p P a_mem
  map_add' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, ← Submodule.Quotient.mk_add,
      quotientToQuotientRangePowQuotSuccAux_mk, mul_add, map_add, map_mul, AddMemClass.mk_add_mk]
  map_smul' x y := by
    induction x, y using Quotient.inductionOn₂' with | _ x y
    simp only [Submodule.Quotient.mk''_eq_mk, RingHom.id_apply,
      quotientToQuotientRangePowQuotSuccAux_mk]
    refine congr_arg Submodule.Quotient.mk ?_
    ext
    simp only [map_mul, Quotient.mk_eq_mk, Submodule.coe_smul_of_tower,
      Algebra.smul_def, CompatQuotient.algebraMap_quotient_pow_ramificationIdx]
    ring

theorem quotientToQuotientRangePowQuotSucc_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_right x _ a_mem)⟩ :=
  quotientToQuotientRangePowQuotSuccAux_mk p P a_mem x

theorem quotientToQuotientRangePowQuotSucc_injective [IsDedekindDomain S] [P.IsPrime]
    {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc p P a_mem) := fun x =>
  Quotient.inductionOn' x fun x y =>
    Quotient.inductionOn' y fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow_right hi
      simp only [Submodule.Quotient.mk''_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
        Submodule.coe_sub] at h ⊢
      rcases h with ⟨⟨z, hz⟩, h⟩
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, ← map_sub, Ideal.Quotient.eq,
        ← mul_sub] at h
      exact
        (Ideal.IsPrime.mem_pow_mul _
              ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_left
          a_notMem

theorem quotientToQuotientRangePowQuotSucc_surjective [IsDedekindDomain S]
    (hP0 : P ≠ ⊥) [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow_right hi.le
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a} ⊔ P ^ (i + 1) by
    obtain ⟨y', hy', z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotientToQuotientRangePowQuotSucc_mk,
      Submodule.Quotient.eq, LinearMap.mem_range, Subtype.ext_iff,
      Submodule.coe_sub]
    refine ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, ?_⟩
    rw [powQuotSuccInclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add,
      sub_add_cancel_left, map_neg]
  rw [← Submodule.span_singleton_le_iff_mem, submodule_span_eq] at a_mem a_notMem
  have hspan0 : span {a} ≠ ⊥ := fun ha ↦ a_notMem (ha ▸ bot_le)
  rwa [sup_comm, Ideal.irreducible_pow_sup hspan0 ((prime_iff_isPrime hP0).mpr hP).irreducible,
    count_normalizedFactors_eq a_mem a_notMem, min_eq_left i.le_succ]

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDedekindDomain S]
    [P.IsPrime] (hP : P ≠ ⊥) {i : ℕ} (hi : i < e) :
    ((P ^ i).map (Ideal.Quotient.mk (P ^ e)) ⧸ LinearMap.range (powQuotSuccInclusion p P i))
      ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_notMem using
    IsConcreteLE.exists_of_lt
      (Ideal.pow_right_strictAnti P hP (Ideal.IsPrime.ne_top inferInstance) (le_refl i.succ))
  refine (LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩).symm
  · exact quotientToQuotientRangePowQuotSucc p P a_mem
  · exact quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem
  · exact quotientToQuotientRangePowQuotSucc_surjective p P hP hi a_mem a_notMem

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
theorem rank_pow_quot_aux [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    {i : ℕ} (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) +
        Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ (i + 1))) := by
  rw [← rank_range_of_injective _ (powQuotSuccInclusion_injective p P i),
    (quotientRangePowQuotSuccInclusionEquiv p P hP0 hi).symm.rank_eq]
  exact (Submodule.rank_quotient_add_rank (LinearMap.range (powQuotSuccInclusion p P i))).symm

theorem rank_pow_quot [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)) =
      (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
  let Q : ℕ → Prop :=
    fun i => Module.rank (R ⧸ p) { x // x ∈ map (Ideal.Quotient.mk (P ^ e)) (P ^ i) }
      = (e - i) • Module.rank (R ⧸ p) (S ⧸ P)
  refine Nat.decreasingInduction' (P := Q) (fun j lt_e _le_j ih => ?_) hi ?_
  · dsimp only [Q]
    rw [rank_pow_quot_aux p P _ lt_e, ih, ← succ_nsmul', Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt lt_e)]
    assumption
  · dsimp only [Q]
    rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    exact rank_bot (R ⧸ p) (S ⧸ P ^ e)

end

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
theorem rank_prime_pow_ramificationIdx [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime]
    (hP0 : P ≠ ⊥) (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @CompatQuotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  let : NeZero e := ⟨he⟩
  have := rank_pow_quot p P hP0 0 (Nat.zero_le e)
  rw [pow_zero, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  exact (rank_top (R ⧸ p) _).symm.trans this

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
theorem finrank_prime_pow_ramificationIdx [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [p.IsMaximal] [P.IsPrime] (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <|
            @CompatQuotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ _ _ ⟨he⟩) := by
  let : NeZero e := ⟨he⟩
  let : Algebra (R ⧸ p) (S ⧸ P) :=
    CompatQuotient.algebraQuotientOfRamificationIdxNeZero p P
  have hdim := rank_prime_pow_ramificationIdx _ _ hP0 he
  by_cases hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  · have := (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    apply @Nat.cast_injective Cardinal
    rw [finrank_eq_rank', Nat.cast_mul, finrank_eq_rank', hdim, nsmul_eq_mul]
  have hPe := mt (finiteDimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe,
    mul_zero]

end FactLeComap


end AlgebraicCurves.Compat.FinrankPrimePow
