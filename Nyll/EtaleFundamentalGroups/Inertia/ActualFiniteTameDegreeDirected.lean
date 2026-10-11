/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteTameRootsSystem
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameOrderTower
import Mathlib.FieldTheory.Galois.GaloisClosure

/-!
# Directedness of the actual finite tame degrees

The literal range of the actual tame index is nonempty and directed by
divisibility. Its upper bounds are supplied by finite Galois composita.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- A finite base stage supplies an actual tame degree. -/
theorem actualFiniteTameDegreeSet_nonempty :
    (actualFiniteTameDegreeSet A K L Q).Nonempty := by
  exact ⟨actualFiniteStageTameIndex A K L Q ⊥, ⊥, rfl⟩

/-- Actual finite Galois composita direct the literal tame-degree range. -/
theorem actualFiniteTameDegreeSet_directed :
    Directed (· ≤ ·) (id : actualFiniteTameDegreeSet A K L Q →
      actualFiniteTameDegreeSet A K L Q) := by
  intro m n
  obtain ⟨E, hE⟩ := m.property
  obtain ⟨F, hF⟩ := n.property
  refine ⟨⟨actualFiniteStageTameIndex A K L Q (E ⊔ F), E ⊔ F, rfl⟩, ?_, ?_⟩
  · change m.val.val ∣ actualFiniteStageTameOrder A K L Q (E ⊔ F)
    rw [← hE]
    exact actualFiniteStageTameOrder_dvd_of_le A K L Q E (E ⊔ F) le_sup_left
  · change n.val.val ∣ actualFiniteStageTameOrder A K L Q (E ⊔ F)
    rw [← hF]
    exact actualFiniteStageTameOrder_dvd_of_le A K L Q F (E ⊔ F) le_sup_right

end EtaleFundamentalGroups.Inertia
