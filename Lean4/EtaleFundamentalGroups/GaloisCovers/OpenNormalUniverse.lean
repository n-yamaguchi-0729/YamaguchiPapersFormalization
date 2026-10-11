/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenNormal

/-!
# Open normal subgroups across fiber-functor universes

The usual quotient construction for a fiber functor can live in a larger
universe than its finite fibers.  This file removes that presentation-level
restriction by switching the universe of the fiber functor, applying the
quotient construction there, and transporting the distinguished point back.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- Every open normal subgroup of the automorphism group of an arbitrary
fiber functor is the stabilizer of a point on a Galois object, without a
restriction relating the universe of the fibers to that of the category. -/
theorem exists_galois_object_point_stabilizer_eq_any_universe
    (U : OpenNormalSubgroup (Aut F)) :
    ∃ (X : C) (_ : IsGalois X) (x : F.obj X),
      MulAction.stabilizer (Aut F) x = (U : Subgroup (Aut F)) := by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  let : FiberFunctor F' := FiberFunctor.comp_right _
  let eF : Aut F ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight F
      (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFunctor
  let U' : OpenNormalSubgroup (Aut F') :=
    ProCGroups.ProC.OpenNormalSubgroup.map
      (ContinuousMonoidHom.toContinuousMonoidHom eF)
      (Homeomorph.isOpenMap eF.toHomeomorph) eF.surjective U
  obtain ⟨X, hX, x', hx'⟩ :=
    exists_galois_object_point_stabilizer_eq F' U'
  let eX : F'.obj X ≃ F.obj X := FintypeCat.uSwitchEquiv (F.obj X)
  let x : F.obj X := eX x'
  refine ⟨X, hX, x, ?_⟩
  ext g
  change g • x = x ↔ g ∈ (U : Subgroup (Aut F))
  have htransport : eX ((eF g) • x') = g • eX x' := by
    change (F.obj X).uSwitchEquiv
        (((eF g).hom.app X) x') =
      g.hom.app X ((F.obj X).uSwitchEquiv x')
    change (F.obj X).uSwitchEquiv
        (FintypeCat.uSwitch.map (g.hom.app X) x') =
      g.hom.app X ((F.obj X).uSwitchEquiv x')
    exact (FintypeCat.uSwitchEquiv_naturality (g.hom.app X) x').symm
  calc
    g • x = x ↔ (eF g) • x' = x' := by
      change g • eX x' = eX x' ↔ (eF g) • x' = x'
      rw [← htransport]
      exact eX.injective.eq_iff
    _ ↔ eF g ∈ MulAction.stabilizer (Aut F') x' :=
      MulAction.mem_stabilizer_iff.symm
    _ ↔ eF g ∈ (U' : Subgroup (Aut F')) := by rw [hx']
    _ ↔ g ∈ (U : Subgroup (Aut F)) := by
      dsimp only [U']
      change eF g ∈
          (U : Subgroup (Aut F)).map eF.toMonoidHom ↔
        g ∈ (U : Subgroup (Aut F))
      constructor
      · rintro ⟨a, ha, hga⟩
        have : a = g := eF.injective hga
        simpa [this] using ha
      · intro hg
        exact ⟨g, hg, rfl⟩

end CategoryTheory.PreGaloisCategory
