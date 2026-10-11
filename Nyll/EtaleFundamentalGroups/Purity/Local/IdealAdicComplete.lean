/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Adic completeness for ideals in a complete Noetherian local ring

A finite module over a Noetherian local ring that is complete for the
maximal-ideal filtration is complete for every finer ideal-adic filtration.
The key point is that the submodules `I ^ n • M` are closed for the
maximal-adic topology: their quotients are finite modules and hence
maximal-adically Hausdorff.
-/

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups.Purity

universe u v

/-- A finite module over a Noetherian local ring, complete for the maximal
ideal, is complete for every ideal contained in the maximal ideal. -/
theorem isAdicComplete_of_le_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    [IsAdicComplete (maximalIdeal R) M] :
    IsAdicComplete I M := by
  refine
    { toIsHausdorff :=
        IsHausdorff.of_le_jacobson I M
          (hI.trans (maximalIdeal_le_jacobson (⊥ : Ideal R)))
      toIsPrecomplete := ?_ }
  refine ⟨fun f hf ↦ ?_⟩
  have hfMaximal :
      ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n
          [SMOD ((maximalIdeal R) ^ m • ⊤ : Submodule R M)] := by
    intro m n hmn
    exact SModEq.mono
      (Submodule.smul_mono (Ideal.pow_right_mono hI m) le_rfl)
      (hf hmn)
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec
      (inferInstance : IsPrecomplete (maximalIdeal R) M) hfMaximal
  refine ⟨L, fun n ↦ ?_⟩
  let N : Submodule R M := I ^ n • ⊤
  let Q := M ⧸ N
  let q : M →ₗ[R] Q := N.mkQ
  let : Module.Finite R Q := Module.Finite.quotient R N
  have hq : q (f n) = q L := by
    rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
    intro k
    let t := max n k
    have hnt : n ≤ t := Nat.le_max_left n k
    have hkt : k ≤ t := Nat.le_max_right n k
    have hfnft : q (f n) = q (f t) := by
      change Submodule.Quotient.mk (f n) = Submodule.Quotient.mk (f t)
      exact hf hnt
    rw [hfnft]
    have htail :
        f t ≡ L
          [SMOD ((maximalIdeal R) ^ k • ⊤ : Submodule R M)] :=
      SModEq.mono (Submodule.pow_smul_top_le (maximalIdeal R) M hkt) (hL t)
    have hmapped := htail.map q
    simpa only [q, Q, Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective N)] using hmapped
  change Submodule.Quotient.mk (f n) = Submodule.Quotient.mk L
  exact hq

end EtaleFundamentalGroups.Purity

end
