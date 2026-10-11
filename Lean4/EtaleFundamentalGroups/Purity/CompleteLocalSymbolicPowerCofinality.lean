/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CompleteLocalSymbolicPowers
import EtaleFundamentalGroups.Purity.SymbolicPowerErrorModule
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Module

/-!
# Cofinality of symbolic and ordinary prime powers

For a prime with quotient of dimension at most one in a complete
Noetherian local domain, sufficiently deep symbolic powers lie in any
specified ordinary power.  Modulo that ordinary power, the symbolic-power
images lie in an Artinian module and hence stabilize.  Chevalley's lemma
places the stable image in every maximal-ideal power, so Hausdorffness of
the finite quotient forces it to vanish.
-/

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]

/-- Symbolic powers of a prime with quotient dimension at most one are
cofinal with its ordinary powers in a complete local domain. -/
theorem exists_primeSymbolicPower_le_pow
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ (1 : WithBot ℕ∞)) (n : ℕ) :
    ∃ m : ℕ, primeSymbolicPower P m ≤ P ^ n := by
  let q : R →ₗ[R] R ⧸ P ^ n := Submodule.mkQ (P ^ n)
  let K : Submodule R (R ⧸ P ^ n) :=
    Submodule.map q (primeSymbolicPower P n)
  let : IsArtinian R K := isArtinian_primeSymbolicPower_quotient_pow P hdim n
  let F : ℕ → Submodule R (R ⧸ P ^ n) :=
    fun i => Submodule.map q (primeSymbolicPower P (n + i))
  have hF (i : ℕ) : F i ≤ K :=
    Submodule.map_mono (primeSymbolicPower_antitone P (Nat.le_add_right n i))
  let G : ℕ →o (Submodule R K)ᵒᵈ :=
    { toFun := fun i => (F i).comap K.subtype
      monotone' := fun _ _ hij =>
        Submodule.comap_mono (Submodule.map_mono
          (primeSymbolicPower_antitone P (Nat.add_le_add_left hij n))) }
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes G
  refine ⟨n + N, ?_⟩
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero (P ^ n)).mp
  have hxF : q x ∈ F N := Submodule.mem_map_of_mem (f := q) hx
  let y : K := ⟨q x, hF N hxF⟩
  have hy : y ∈ (G N).ofDual := hxF
  change q x = 0
  apply IsHausdorff.haus (inferInstance : IsHausdorff (maximalIdeal R) (R ⧸ P ^ n))
  intro k
  apply SModEq.zero.mpr
  obtain ⟨m, hm⟩ := exists_primeSymbolicPower_le_maximalIdeal_pow P k
  have hy' : y ∈ (G (max N m)).ofDual :=
    (hN (max N m) (le_max_left N m)) ▸ hy
  have hxF' : q x ∈ F (max N m) := hy'
  have hsmall : primeSymbolicPower P (n + max N m) ≤ maximalIdeal R ^ k :=
    (primeSymbolicPower_antitone P
      ((le_max_right N m).trans (Nat.le_add_left (max N m) n))).trans hm
  have hxmap : q x ∈ Submodule.map q (maximalIdeal R ^ k) :=
    Submodule.map_mono hsmall hxF'
  obtain ⟨a, ha, heq⟩ := Submodule.mem_map.mp hxmap
  have ha' : a ∈ ((maximalIdeal R ^ k) • ⊤ : Submodule R R) := by
    simpa only [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one] using ha
  have hmap := Submodule.mem_map_of_mem (f := q) ha'
  rw [Submodule.map_smul'', Submodule.map_top] at hmap
  rw [Submodule.range_mkQ] at hmap
  rw [heq] at hmap
  exact hmap

end EtaleFundamentalGroups.Purity

end
