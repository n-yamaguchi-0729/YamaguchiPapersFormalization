/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.FiniteH1Surjectivity

/-! # Formal Hilbert 90 under a topological group isomorphism -/

namespace Yamaguchi26AbfaithfulGalois
universe u v
variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {G' : Type v} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- Transport actual finite cocycles along each induced open-subgroup isomorphism. -/
theorem formalHilbert90_comp_continuousMulEquiv
    (θ : Orientation p G') (e : G ≃ₜ* G') (hθ : FormalHilbert90 θ) :
    FormalHilbert90 (θ.comp (e : G →ₜ* G')) := by
  intro H n hn
  let H' : OpenSubgroup G' := H.comap e.symm.toMonoidHom e.symm.continuous
  let f : (H : Subgroup G) ≃ₜ* (H' : Subgroup G') :=
    { toFun := fun x => ⟨e x, by
        change e.symm (e x) ∈ H
        rw [e.symm_apply_apply]
        exact x.property⟩
      invFun := fun y => ⟨e.symm y, y.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (map_mul e (x : G) (y : G))
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk
        (fun x => by
          change e.symm (e x) ∈ H
          rw [e.symm_apply_apply]
          exact x.property)
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk
        (fun y => y.property) }
  apply h1_reduction_surjective_of_finiteCocycle_lifting
  intro c
  let c' : FiniteCocycle θ (H' : Subgroup G') 1 :=
    { toFun := fun y => c.toFun (f.symm y)
      continuous_toFun := c.continuous_toFun.comp f.symm.continuous
      cocycle := by
        intro x y
        rw [map_mul, c.cocycle]
        change c.toFun (f.symm x) + (PadicInt.toZModPow 1) (θ (e (e.symm x)) : PadicInt p) *
          c.toFun (f.symm y) = _
        rw [e.apply_symm_apply] }
  obtain ⟨d', hd'⟩ := finiteCocycle_lift_mod_one_of_h1 θ (H' : Subgroup G') n hn
    (hθ H' n hn) c'
  let d : FiniteCocycle (θ.comp (e : G →ₜ* G')) (H : Subgroup G) n :=
    { toFun := fun x => d'.toFun (f x)
      continuous_toFun := d'.continuous_toFun.comp f.continuous
      cocycle := by
        intro x y
        rw [map_mul, d'.cocycle]
        rfl }
  refine ⟨d, ?_⟩
  intro x
  change ZMod.castHom _ (ZMod (p ^ 1)) (d'.toFun (f x)) = c.toFun x
  exact (hd' (f x)).trans (congrArg c.toFun (f.symm_apply_apply x))

end Yamaguchi26AbfaithfulGalois
