/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.PadicCharacters

/-! # Torsion and fixed classes under relative formal Hilbert 90 -/

namespace Yamaguchi26AbfaithfulGalois

universe u

/-- The primary abelianization of the orientation kernel is torsion-free. -/
theorem primaryAbelianization_isMulTorsionFree
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ) :
    IsMulTorsionFree (PrimaryAbelianization ℓ D) := by
  constructor
  intro n hn x y hxy
  by_contra hne
  have hne' : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨U, hDU, c, hc⟩ := exists_padicCocycle_detecting_primary
    D hDclosed θ hDθ hLift (x * y⁻¹) hne'
  let f := c.primaryCharacter D hDclosed hDθ hDU
  have heq : f x = f y := by
    apply IsMulTorsionFree.pow_left_injective hn
    change (f x) ^ n = (f y) ^ n
    rw [← map_pow, ← map_pow]
    exact congrArg f hxy
  apply hc
  change (f (x * y⁻¹)).toAdd = 0
  rw [map_mul, map_inv, heq, mul_inv_cancel]
  rfl

/-- Infinite orientation image forces every open-subgroup fixed part to vanish. -/
theorem primaryFixedSubgroup_eq_bot_of_infinite_orientation
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hDclosed : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ) (hθ : Set.Infinite (Set.range θ))
    (H : OpenSubgroup G) : primaryFixedSubgroup ℓ D hDclosed (H : Subgroup G) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  by_contra hne
  obtain ⟨U, hDU, c, hc⟩ := exists_padicCocycle_detecting_primary
    D hDclosed θ hDθ hLift a hne
  have hker : (U : Subgroup G) ⊓ (H : Subgroup G) ≤ θ.toMonoidHom.ker := by
    intro g hg
    have hconj := c.primaryCharacter_conj D hDclosed hDθ hDU ⟨g, hg.1⟩ a
    rw [ha ⟨g, hg.2⟩] at hconj
    apply Units.ext
    change (θ g : PadicInt ℓ) = 1
    apply mul_right_cancel₀ hc
    exact hconj.symm.trans (one_mul _).symm
  have hopen : IsOpen (θ.toMonoidHom.ker : Set G) :=
    Subgroup.isOpen_mono hker (U.isOpen.inter H.isOpen)
  let K : OpenNormalSubgroup G :=
    { toSubgroup := θ.toMonoidHom.ker
      isOpen' := hopen }
  let : Finite (G ⧸ θ.toMonoidHom.ker) :=
    ProCGroups.ProC.OpenNormalSubgroup.quotientFinite K
  let : Finite θ.toMonoidHom.range :=
    Finite.of_equiv (G ⧸ θ.toMonoidHom.ker)
      (QuotientGroup.quotientKerEquivRange θ.toMonoidHom).toEquiv
  apply hθ
  change Set.Finite (θ.toMonoidHom.range : Set (PadicInt ℓ)ˣ)
  exact Set.toFinite _

end Yamaguchi26AbfaithfulGalois
