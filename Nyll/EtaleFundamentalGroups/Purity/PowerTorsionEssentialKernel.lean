/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.RingTheory.Ideal.Operations

/-!
# Essential scalar kernels in power-torsion modules

If every element of a module is killed by a power of a scalar, the kernel
of multiplication by that scalar is essential.  On a submodule disjoint
from the kernel, induction on the annihilating exponent forces every
element to be zero.  Local cohomology supplies the required power torsion
for each scalar in its support ideal.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]

/-- The scalar kernel is essential when each element is killed by some
power of that scalar. -/
theorem isEssentialSubmodule_ker_smul_of_power_torsion
    {M : Type v} [AddCommGroup M] [Module R M]
    (x : R) (hM : ∀ m : M, ∃ n : ℕ, x ^ n • m = 0) :
    IsEssentialSubmodule
      (LinearMap.ker (x • (LinearMap.id : M →ₗ[R] M))) := by
  intro L hL
  have hkill : ∀ (n : ℕ) (m : M), m ∈ L → x ^ n • m = 0 → m = 0 := by
    intro n
    induction n with
    | zero =>
        intro m _hm hn
        simpa only [pow_zero, one_smul] using hn
    | succ n ih =>
        intro m hm hn
        have hxm : x • m = 0 :=
          ih (x • m) (L.smul_mem x hm)
            (by simpa only [pow_succ, mul_smul] using hn)
        have hmker : m ∈ LinearMap.ker (x • (LinearMap.id : M →ₗ[R] M)) := by
          change x • m = 0
          exact hxm
        exact (Submodule.disjoint_def.mp hL) m hmker hm
  apply le_antisymm ?_ bot_le
  intro m hm
  obtain ⟨n, hn⟩ := hM m
  exact (Submodule.mem_bot R).mpr (hkill n m hm hn)

/-- A scalar in the support ideal has essential kernel on the actual
derived local-cohomology module. -/
theorem isEssentialSubmodule_ker_smul_derivedLocalCohomologyModule
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (x : R) (hx : x ∈ I) :
    IsEssentialSubmodule
      (LinearMap.ker
        (x • (LinearMap.id : derivedLocalCohomologyModule I M i →ₗ[R]
          derivedLocalCohomologyModule I M i))) := by
  apply isEssentialSubmodule_ker_smul_of_power_torsion x
  intro z
  obtain ⟨n, hn⟩ :=
    derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero I M i z
  exact ⟨n, hn (x ^ n) (Ideal.pow_mem_pow hx n)⟩

end EtaleFundamentalGroups.Purity
