/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.PadicCharacters
import Nyll.GaloisCohomology.ProfiniteIntegers.PadicCharacterSurjectivity

/-! # A p-adic quotient from trivial-orientation formal Hilbert 90 -/

namespace Yamaguchi26AbfaithfulGalois
universe u
variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- A nonzero prime cyclic character lifts to a surjective p-adic character
when the trivial orientation satisfies formal Hilbert 90. -/
theorem exists_surjective_padic_character_of_formalHilbert90_trivial
    (hF : FormalHilbert90 (1 : Orientation p G))
    (χ : G →ₜ* Multiplicative (ZMod p)) (hχ : ∃ g : G, χ g ≠ 1) :
    ∃ ν : G →ₜ* Multiplicative (PadicInt p), Function.Surjective ν := by
  let e : ZMod p ≃+* ZMod (p ^ 1) := ZMod.ringEquivCongr (pow_one p).symm
  let c : FiniteCocycle (1 : Orientation p G) ⊤ 1 :=
    { toFun := fun x => e (χ (x : G)).toAdd
      continuous_toFun := continuous_of_discreteTopology.comp
        (χ.continuous.comp continuous_subtype_val)
      cocycle := by
        intro x y
        rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one,
          map_one, one_mul]
        change e (χ ((x : G) * (y : G))).toAdd =
          e (χ (x : G)).toAdd + e (χ (y : G)).toAdd
        rw [map_mul]
        exact map_add e _ _ }
  obtain ⟨d, hd⟩ := finiteCocycle_lift_padic_of_fixed_group
    (1 : Orientation p G) ⊤ (hF ⊤) 1 (by decide) c
  let ν : G →ₜ* Multiplicative (PadicInt p) :=
    { toFun := fun x => Multiplicative.ofAdd (d.toFun ⟨x, Subgroup.mem_top x⟩)
      map_one' := d.map_one
      map_mul' := by
        intro x y
        change d.toFun (⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩) =
          d.toFun ⟨x, Subgroup.mem_top x⟩ + d.toFun ⟨y, Subgroup.mem_top y⟩
        rw [d.cocycle]
        rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, one_mul]
      continuous_toFun := d.continuous_toFun.comp
        (continuous_id.subtype_mk (fun x => Subgroup.mem_top x)) }
  refine ⟨ν, PadicInt.surjective_character_of_nonzero_reduction ν ?_⟩
  obtain ⟨g, hg⟩ := hχ
  refine ⟨g, ?_⟩
  change PadicInt.toZModPow 1 (d.toFun ⟨g, Subgroup.mem_top g⟩) ≠ 0
  rw [hd]
  intro hzero
  apply hg
  apply Multiplicative.toAdd.injective
  exact e.injective (hzero.trans (map_zero e).symm)

end Yamaguchi26AbfaithfulGalois
