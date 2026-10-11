/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Power torsion for the sum of two ideals

The binomial bound `(I + J)^(n + m) ≤ I^n + J^m` identifies power torsion
for a sum with the intersection of the two power-torsion submodules. This
also constructs the linear equivalence needed to iterate principal torsion
in the finite Čech complex.
-/

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Power torsion for a sum is the intersection of the power-torsion
submodules for the two summands. -/
theorem primaryComponent_ideal_sup (I J : Ideal R) :
    Ideal.primaryComponent M (I ⊔ J) =
      Ideal.primaryComponent M I ⊓ Ideal.primaryComponent M J := by
  ext y
  simp only [Submodule.mem_inf, Ideal.primaryComponent_mem,
    Submodule.mem_torsionBySet_iff, SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨⟨n, fun a ha => hn a
      ((show I ^ n ≤ (I ⊔ J) ^ n from pow_le_pow_left' le_sup_left n) ha)⟩,
      ⟨n, fun a ha => hn a
        ((show J ^ n ≤ (I ⊔ J) ^ n from pow_le_pow_left' le_sup_right n) ha)⟩⟩
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    refine ⟨n + m, ?_⟩
    intro c hc
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      ((Ideal.sup_pow_add_le_pow_sup_pow (I := I) (J := J) (n := n) (m := m)) hc)
    calc
      c • y = (a + b) • y := congrArg (fun r : R => r • y) hab.symm
      _ = a • y + b • y := add_smul a b y
      _ = 0 := by rw [hn a ha, hm b hb, add_zero]

private theorem primaryComponent_submodule (N : Submodule R M) (J : Ideal R) :
    Ideal.primaryComponent N J = (Ideal.primaryComponent M J).comap N.subtype := by
  ext z
  change (z ∈ Ideal.primaryComponent N J) ↔
    ((z : M) ∈ Ideal.primaryComponent M J)
  simp only [Ideal.primaryComponent_mem, Submodule.mem_torsionBySet_iff,
    SetLike.coe_sort_coe, Subtype.forall]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a ha => congrArg (fun t : N => (t : M)) (hn a ha)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a ha => Subtype.ext (hn a ha)⟩

private theorem primaryComponent_iterated_eq_comap (I J : Ideal R) :
    Ideal.primaryComponent (Ideal.primaryComponent M I) J =
      (Ideal.primaryComponent M (I ⊔ J)).comap (Ideal.primaryComponent M I).subtype := by
  rw [primaryComponent_submodule]
  ext z
  change ((z : M) ∈ Ideal.primaryComponent M J) ↔
    ((z : M) ∈ Ideal.primaryComponent M (I ⊔ J))
  rw [primaryComponent_ideal_sup]
  exact ⟨fun h => ⟨z.property, h⟩, fun h => h.2⟩

/-- Iterating ideal-power torsion is canonically equivalent to torsion
for the sum ideal. -/
noncomputable def primaryComponentIteratedLinearEquiv (I J : Ideal R) :
    Ideal.primaryComponent (Ideal.primaryComponent M I) J ≃ₗ[R]
      Ideal.primaryComponent M (I ⊔ J) :=
  (LinearEquiv.ofEq _ _ (primaryComponent_iterated_eq_comap M I J)).trans
    (Submodule.comapSubtypeEquivOfLe (show Ideal.primaryComponent M (I ⊔ J) ≤
      Ideal.primaryComponent M I from by rw [primaryComponent_ideal_sup]; exact inf_le_left))

/-- The iterated torsion equivalence preserves the underlying vector. -/
theorem primaryComponentIteratedLinearEquiv_apply_val (I J : Ideal R)
    (z : Ideal.primaryComponent (Ideal.primaryComponent M I) J) :
    (primaryComponentIteratedLinearEquiv M I J z : M) = (z.1 : M) := by
  simp only [primaryComponentIteratedLinearEquiv, LinearEquiv.trans_apply,
    Submodule.comapSubtypeEquivOfLe_apply_coe, LinearEquiv.coe_ofEq_apply]

end EtaleFundamentalGroups.Purity
