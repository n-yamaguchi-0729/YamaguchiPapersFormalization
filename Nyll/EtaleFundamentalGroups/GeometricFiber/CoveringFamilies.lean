/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Covering families over a field

This file proves Stacks Project, Tag `03QS`: under the geometric-fiber
correspondence, covering families in the small étale site of a field correspond
to jointly surjective families of maps of sets.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A family in the small étale site of a field is covering exactly when its
maps on the fiber at a separably closed geometric point are jointly
surjective. -/
@[stacks 03QS]
theorem ofArrows_mem_smallEtaleTopology_iff_geometricFiber_jointlySurjective
    {k Ω : Type u} [Field k] [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of k))
    {W : (Spec (.of k)).Etale} {ι : Type*}
    {Z : ι → (Spec (.of k)).Etale} (f : ∀ i, Z i ⟶ W) :
    Sieve.ofArrows Z f ∈ smallEtaleTopology (Spec (.of k)) W ↔
      Presieve.ofArrows Z f ∈
        Types.jointlySurjectivePrecoverage.comap
          (Etale.forget (Spec (.of k)) ⋙ coyoneda.obj (op (Over.mk s))) W := by
  rw [ofArrows_mem_smallEtaleTopology_iff,
    Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  constructor
  · intro h x
    have hx :
        x.left (default : Spec (.of Ω)) ∈ ⋃ i, Set.range (f i).left := by
      rw [h]
      exact Set.mem_univ _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z, hz⟩ := hi
    obtain ⟨l, hl, -⟩ :=
      exists_fac_of_etale_of_isSepClosed (f i).left x.left z hz
    let fi : (Z i).left ⟶ W.left := (f i).left
    let zh : (Z i).left ⟶ Spec (.of k) := (Z i).hom
    let wh : W.left ⟶ Spec (.of k) := W.hom
    have hfw : fi ≫ wh = zh := (f i).w
    have hxw : x.left ≫ wh = s := x.w
    let y : Over.mk s ⟶ (Z i).toComma :=
      Over.homMk l (by
        change l ≫ zh = s
        rw [← hfw, ← Category.assoc, hl]
        exact hxw)
    refine ⟨i, y, ?_⟩
    change y ≫ (f i).hom = x
    apply Over.OverMorphism.ext
    exact hl
  · intro h
    apply Set.eq_univ_of_forall
    intro w
    let : Etale (W.left ↘ Spec (.of k)) := W.prop
    have hbase :
        (W.left ↘ Spec (.of k)) w = s (default : Spec (.of Ω)) := by
      exact Subsingleton.elim _ _
    obtain ⟨l, hl, hw⟩ :=
      exists_fac_of_etale_of_isSepClosed (W.left ↘ Spec (.of k)) s w hbase
    let x : Over.mk s ⟶ W.toComma := Over.homMk l hl
    obtain ⟨i, y, hy⟩ := h x
    let yl : Spec (.of Ω) ⟶ (Z i).left := y.left
    let fi : (Z i).left ⟶ W.left := (f i).left
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine ⟨yl (default : Spec (.of Ω)), ?_⟩
    change y ≫ (f i).hom = x at hy
    have hyLeft := congrArg (fun q : Over.mk s ⟶ W.toComma ↦ q.left) hy
    change yl ≫ fi = l at hyLeft
    calc
      fi (yl (default : Spec (.of Ω))) =
          (yl ≫ fi) (default : Spec (.of Ω)) :=
        (Scheme.Hom.comp_apply yl fi (default : Spec (.of Ω))).symm
      _ = l (default : Spec (.of Ω)) :=
        congrArg (fun q : Spec (.of Ω) ⟶ W.left ↦
          q (default : Spec (.of Ω))) hyLeft
      _ = w := hw

end AlgebraicGeometry.Scheme
