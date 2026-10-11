/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.PrimaryTransfer
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.PadicCharacters

/-!
# Inclusion of fixed primary classes

Under relative formal Hilbert 90, globally fixed primary classes inject
into the primary abelianization of the ambient group.
-/

namespace Yamaguchi26AbfaithfulGalois
open ProCGroups.Abelian ProCGroups.ProC
universe u

theorem primaryFixed_eq_one_of_inclusion_eq_one
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ)
    (a : PrimaryAbelianization ℓ D)
    (ha : a ∈ primaryFixedSubgroup ℓ D hD (⊤ : Subgroup G))
    (hzero : primaryInclusionMap ℓ D hD a = 1) : a = 1 := by
  by_contra hne
  obtain ⟨U, hDU, c, hc⟩ :=
    exists_padicCocycle_detecting_primary D hD θ hDθ hLift a hne
  let f := c.primaryCharacter D hD hDθ hDU
  have hUθ : (U : Subgroup G) ≤ θ.toMonoidHom.ker := by
    intro u hu
    have hconj := c.primaryCharacter_conj D hD hDθ hDU ⟨u, hu⟩ a
    rw [ha (⟨u, Subgroup.mem_top u⟩ : (⊤ : Subgroup G))] at hconj
    have heq : (θ u : PadicInt ℓ) = 1 :=
      mul_right_cancel₀ hc (hconj.symm.trans (one_mul _).symm)
    exact Units.ext heq
  let χ : (U : Subgroup G) →ₜ* Multiplicative (PadicInt ℓ) :=
    { toFun := fun u => Multiplicative.ofAdd (c.toFun u)
      map_one' := c.map_one
      map_mul' := by
        intro u v
        change c.toFun (u * v) = c.toFun u + c.toFun v
        rw [c.cocycle, show θ (u : G) = 1 from hUθ u.property, Units.val_one, one_mul]
      continuous_toFun := c.continuous_toFun }
  obtain ⟨F, hF⟩ := exists_primaryCharacter_transfer_fixed D hD U hDU χ f (by
    intro d
    exact (c.primaryCharacter_mk D hD hDθ hDU d).symm)
  have heval := hF a ha
  rw [hzero, map_one] at heval
  have hpow : Nat.card (G ⧸ (U : Subgroup G)) • (f a).toAdd = 0 :=
    congrArg Multiplicative.toAdd heval.symm
  rw [nsmul_eq_mul] at hpow
  have hcard : (Nat.card (G ⧸ (U : Subgroup G)) : PadicInt ℓ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  exact hc ((mul_eq_zero.mp hpow).resolve_left hcard)

/-- Global fixed primary classes inject into the primary abelianization of the
ambient group under the relative formal Hilbert 90 hypothesis. -/
theorem primaryInclusionMap_injective_on_fixed
    {ℓ : ℕ} [Fact ℓ.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (θ : Orientation ℓ G) (hDθ : D ≤ θ.toMonoidHom.ker)
    (hLift : RelativeFormalHilbert90 D θ) :
    Function.Injective
      (fun a : primaryFixedSubgroup ℓ D hD (⊤ : Subgroup G) =>
        primaryInclusionMap ℓ D hD (a : PrimaryAbelianization ℓ D)) := by
  intro a b hab
  change primaryInclusionMap ℓ D hD (a : PrimaryAbelianization ℓ D) =
    primaryInclusionMap ℓ D hD (b : PrimaryAbelianization ℓ D) at hab
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  apply primaryFixed_eq_one_of_inclusion_eq_one D hD θ hDθ hLift
  · exact (primaryFixedSubgroup ℓ D hD (⊤ : Subgroup G)).mul_mem a.property
      ((primaryFixedSubgroup ℓ D hD (⊤ : Subgroup G)).inv_mem b.property)
  · rw [map_mul, map_inv, hab, mul_inv_cancel]

end Yamaguchi26AbfaithfulGalois
