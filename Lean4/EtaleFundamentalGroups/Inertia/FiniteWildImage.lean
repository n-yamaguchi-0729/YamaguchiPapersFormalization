/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow

/-!
# Surjective images of distinguished finite p-subgroups

A normal p-subgroup of prime-to-p index is the unique Sylow subgroup.
Consequently a surjective homomorphism sends any p-subgroup of prime-to-p
index onto that distinguished subgroup. No preservation premise is used.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- A surjective homomorphism of finite groups maps a p-subgroup of
prime-to-p index onto the normal p-subgroup of prime-to-p index in the target.
Both preservation and element lifting follow from this literal image equality. -/
theorem map_eq_of_isPGroup_of_index_not_dvd
    (p : ℕ) [Fact p.Prime]
    {G : Type u} {H : Type v} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (P : Subgroup G) (Q : Subgroup H) [Q.Normal]
    (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPindex : ¬ p ∣ P.index) (hQindex : ¬ p ∣ Q.index) :
    P.map f = Q := by
  let S : Sylow p G := hP.toSylow hPindex
  let T : Sylow p H := S.mapSurjective hf
  have hQT : Q ≤ (T : Subgroup H) := hQ.le_sylow_of_normal T
  have hTQ : (T : Subgroup H) = Q :=
    (hQ.toSylow hQindex).is_maximal' T.isPGroup' hQT
  exact hTQ

end EtaleFundamentalGroups.Inertia
