/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.ContinuousActions.RestrictionFullyFaithful
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Essential image of restriction of finite continuous actions

For a surjective continuous group homomorphism, a finite continuous action is
obtained by restriction exactly when the kernel acts trivially.
-/

@[expose] public section

universe g' g w

noncomputable section

open CategoryTheory
open scoped FintypeCatDiscrete

namespace CategoryTheory.ContAction

variable {G' : Type g'} [Group G'] [TopologicalSpace G'] [CompactSpace G']
variable {G : Type g} [Group G] [TopologicalSpace G]
variable [IsTopologicalGroup G] [T2Space G]

/--
A finite continuous `G'`-action descends along a surjective continuous
homomorphism `h : G' → G` exactly when `ker h` acts trivially.
-/
theorem essImage_res_iff_ker_le_ker_ρAut
    (h : G' →ₜ* G) (hs : Function.Surjective h)
    (Y : ContAction FintypeCat.{w} G') :
    (ContAction.res FintypeCat h).essImage Y ↔
      h.toMonoidHom.ker ≤ (Action.ρAut Y.obj).ker := by
  constructor
  · rintro ⟨X, ⟨e⟩⟩ a ha
    have ha1 : h a = 1 := MonoidHom.mem_ker.mp ha
    apply MonoidHom.mem_ker.mpr
    apply Iso.ext
    apply FintypeCat.hom_ext
    intro y
    change (Y.obj.ρ a).hom y = y
    let ef :=
      (forget₂ (ContAction FintypeCat G') FintypeCat).mapIso e
    let x : X.obj.V := ef.inv y
    have hc := ConcreteCategory.congr_hom (e.hom.hom.comm a) x
    change ef.hom ((X.obj.ρ (h a)).hom x) =
      (Y.obj.ρ a).hom (ef.hom x) at hc
    rw [ha1, Action.ρ_one] at hc
    change ef.hom x = (Y.obj.ρ a).hom (ef.hom x) at hc
    have hxy : ef.hom x = y := FintypeCat.inv_hom_id_apply ef y
    rw [hxy] at hc
    exact hc.symm
  · intro hker
    let ρAut : G →* Aut Y.obj.V :=
      h.toMonoidHom.liftOfSurjective hs ⟨Action.ρAut Y.obj, hker⟩
    have ρAut_comp (a : G') :
        ρAut (h a) = Action.ρAut Y.obj a := by
      simpa [ρAut, MonoidHom.liftOfSurjective] using
        h.toMonoidHom.liftOfRightInverse_comp_apply
          (Function.surjInv hs) (Function.rightInverse_surjInv hs)
          ⟨Action.ρAut Y.obj, hker⟩ a
    let A : Action FintypeCat.{w} G :=
      { V := Y.obj.V
        ρ := (Aut.toEnd Y.obj.V).comp ρAut }
    have hA : A.IsContinuous := by
      change ContinuousSMul G
        ((forget₂ (Action FintypeCat G) TopCat).obj A)
      let : DiscreteTopology
          ((forget₂ (Action FintypeCat G) TopCat).obj A) := by
        change DiscreteTopology A.V
        infer_instance
      rw [continuousSMul_iff_stabilizer_isOpen]
      intro y
      have hquot : Topology.IsQuotientMap h :=
        Topology.IsQuotientMap.of_surjective_continuous
          hs h.continuous_toFun
      apply hquot.isCoinducing.isOpen_preimage.mp
      -- Express both stabilizers through their actions before comparing them.
      have hpre :
          h ⁻¹' MulAction.stabilizer G y =
            {a : G' | (Y.obj.ρ a).hom y = y} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        change (ρAut (h a)).hom y = y ↔ (Y.obj.ρ a).hom y = y
        rw [ρAut_comp]
        rfl
      rw [hpre]
      let yY :
          ((forget₂ (Action FintypeCat G') TopCat).obj Y.obj) := y
      let : ContinuousSMul G'
          ((forget₂ (Action FintypeCat G') TopCat).obj Y.obj) :=
        Y.property
      let : DiscreteTopology
          ((forget₂ (Action FintypeCat G') TopCat).obj Y.obj) := by
        change DiscreteTopology Y.obj.V
        infer_instance
      have hopen := stabilizer_isOpen G' yY
      change IsOpen {a : G' | (Y.obj.ρ a).hom yY = yY} at hopen
      exact hopen
    have hrho (a : G') :
        ((Action.res FintypeCat h.toMonoidHom).obj A).ρ a =
          Y.obj.ρ a := by
      change (Aut.toEnd Y.obj.V) (ρAut (h a)) = Y.obj.ρ a
      rw [ρAut_comp]
      rfl
    let eA :
        (Action.res FintypeCat h.toMonoidHom).obj A ≅ Y.obj :=
      Action.mkIso (Iso.refl _) (by
        intro a
        rw [hrho a]
        change Y.obj.ρ a ≫ 𝟙 Y.obj.V = 𝟙 Y.obj.V ≫ Y.obj.ρ a
        simp)
    let X : ContAction FintypeCat.{w} G := ⟨A, hA⟩
    let e : (ContAction.res FintypeCat h).obj X ≅ Y :=
      ObjectProperty.isoMk _ eA
    exact ⟨X, ⟨e⟩⟩

end CategoryTheory.ContAction
