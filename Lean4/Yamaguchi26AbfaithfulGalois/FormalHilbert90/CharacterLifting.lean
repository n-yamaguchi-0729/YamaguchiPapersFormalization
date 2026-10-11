/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CocycleLifting
import ProCGroups.Cohomology.FiniteCharacterExtension

/-! # Lifting characters on the closed kernel of an orientation -/

namespace Yamaguchi26AbfaithfulGalois

universe u

/-- A finite character on the closed kernel of an orientation extends to a
p-adic cocycle on an open normal supergroup, using precisely the relative
formal Hilbert 90 hypothesis. -/
theorem exists_openNormal_padicCocycle_lifting_character
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ)
    (n : ℕ) (hn : 1 ≤ n) (χ : D →ₜ* Multiplicative (ZMod (ℓ ^ n))) :
    ∃ U : OpenNormalSubgroup G, ∃ hDU : D ≤ (U : Subgroup G),
      ∃ c : PadicCocycle θ (U : Subgroup G), ∀ d : D,
        PadicInt.toZModPow n (c.toFun (Subgroup.inclusion hDU d)) = (χ d).toAdd := by
  let θn : G →ₜ* (ZMod (ℓ ^ n))ˣ :=
    { toMonoidHom := (Units.map (PadicInt.toZModPow n).toMonoidHom).comp θ.toMonoidHom
      continuous_toFun := ((PadicInt.continuous_toZModPow n).units_map
        (PadicInt.toZModPow n).toMonoidHom).comp θ.continuous }
  let V : OpenNormalSubgroup G := ProCGroups.ProC.OpenNormalSubgroup.ker θn
  obtain ⟨U, hDU, hUV, η, hη⟩ :=
    ProCGroups.exists_openNormal_character_extension D hDclosed χ V
  have hDθn : D ≤ θn.toMonoidHom.ker := by
    intro d hd
    change Units.map (PadicInt.toZModPow n).toMonoidHom (θ d) = 1
    rw [show θ d = 1 from hDθ hd, map_one]
  have hUθn : (U : Subgroup G) ≤ θn.toMonoidHom.ker :=
    hUV.trans (sup_le hDθn le_rfl)
  let c₀ : FiniteCocycle θ (U : Subgroup G) n :=
    { toFun := fun x => (η x).toAdd
      continuous_toFun := η.continuous
      cocycle := by
        intro x y
        have hθ : PadicInt.toZModPow n (θ (x : G) : PadicInt ℓ) = 1 :=
          congrArg Units.val (hUθn x.2)
        rw [hθ, one_mul]
        exact congrArg Multiplicative.toAdd (map_mul η x y) }
  obtain ⟨c, hc⟩ := finiteCocycle_lift_padic_of_fixed_group θ (U : Subgroup G)
    (hLift U hDU) n hn c₀
  refine ⟨U, hDU, c, ?_⟩
  intro d
  rw [hc]
  exact congrArg Multiplicative.toAdd (hη d)

end Yamaguchi26AbfaithfulGalois
