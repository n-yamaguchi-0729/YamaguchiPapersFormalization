/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Boundary.CyclotomicInversion

/-!
# Transport and triviality of finite quotient ranges

These group-theoretic lemmas transport the range of a finite quotient through
successive homomorphisms without unfolding the quotient construction.
-/

namespace EtaleFundamentalGroups.Inertia

universe uG uH uK uM

/-- If a composite quotient is identified with a canonical homomorphism,
then any subsequent range identification transports back to the original
quotient range. -/
theorem range_map_map_eq_of_comp_eq
    {G : Type uG} {H : Type uH} {K : Type uK} {M : Type uM}
    [Group G] [Group H] [Group K] [Group M]
    (q : G →* H) (f : H →* K) (c : K →* M)
    (u : G →* K) (I : Subgroup M)
    (hcomp : f.comp q = u) (hrange : u.range.map c = I) :
    (q.range.map f).map c = I := by
  calc
    (q.range.map f).map c = (f.comp q).range.map c := by
      rw [MonoidHom.range_comp]
    _ = u.range.map c := by rw [hcomp]
    _ = I := hrange

/-- If a finite quotient range has cardinality prime to every rational prime,
then every subgroup obtained from it by successive range maps is trivial. -/
theorem subgroup_eq_bot_of_range_map_map_eq_of_coprime_every_prime
    {G : Type uG} {H : Type uH} {K : Type uK} {M : Type uM}
    [Group G] [Group H] [Group K] [Group M]
    (q : G →* H) (f : H →* K) (c : K →* M)
    (I : Subgroup M) [Finite q.range]
    (hrange : (q.range.map f).map c = I)
    (hCoprime : ∀ p : ℕ, p.Prime → Nat.Coprime (Nat.card q.range) p) :
    I = ⊥ := by
  have hq : q.range = ⊥ :=
    ProCGroups.Boundary.subgroup_eq_bot_of_card_coprime_every_prime
      q.range hCoprime
  rw [hq] at hrange
  simpa using hrange.symm

end EtaleFundamentalGroups.Inertia
