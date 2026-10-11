/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteStepSolvableQuotients.ProsolvableCriterion
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.GroupTheory.IsPerfect

/-!
# 定理 2.5 に用いる位相的完全核の群論

連続全射 `f : G → Q` に対し、`Q` の任意の開正規部分群 `H` の逆像上で
アーベル化の写像が単射ならば、`ker f` は位相的完全である。
証明では有限商 `q : G → S` ごとに `N = q(ker f)` を作り、`S/N` への写像を
`Q` に降ろす。その核を `H` とすると、局所アーベル化の単射性から `N = [N,N]`
が従う。最後に閉集合への所属を有限商で検出して核の完全性を得る。

ここにはスキームに関する仮定や結論を新しい field として追加していない。
幾何学的な定理 2.5 への適用には、有限 étale 被覆の基本群と開部分群との比較から
局所アーベル化の単射性を実際に導く必要がある。
-/

noncomputable section

open scoped ProCGroupsSolvableQuotients

namespace Yamaguchi26SolvableCoverings

open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- 局所アーベル化が単射である全射の核は、任意の離散商の中で完全群を像に持つ。 -/
theorem isPerfect_kernel_image_of_openNormalAbelianizationInjective
    {G Q S : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    [TopologicalSpace S] [Group S] [DiscreteTopology S]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f)
    (q : G →ₜ* S) (hq : Function.Surjective q) :
    Group.IsPerfect (f.ker.map q.toMonoidHom) := by
  let K : Subgroup G := f.ker
  let N : Subgroup S := K.map q.toMonoidHom
  let : N.Normal :=
    Subgroup.Normal.map (show K.Normal by infer_instance) q.toMonoidHom hq
  let : DiscreteTopology (S ⧸ N) :=
    QuotientGroup.discreteTopology (isOpen_discrete (N : Set S))
  let qN : G →ₜ* S ⧸ N :=
    { toMonoidHom := (QuotientGroup.mk' N).comp q.toMonoidHom
      continuous_toFun := QuotientGroup.continuous_mk.comp q.continuous_toFun }
  have hKqN : f.ker ≤ qN.ker := by
    intro x hx
    apply MonoidHom.mem_ker.mpr
    apply (QuotientGroup.eq_one_iff (N := N) (q x)).2
    exact ⟨x, hx, rfl⟩
  let r₀ : Q →* S ⧸ N :=
    f.toMonoidHom.liftOfSurjective hf ⟨qN.toMonoidHom, hKqN⟩
  have hcomp : r₀.comp f.toMonoidHom = qN.toMonoidHom := by
    ext x
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := f.toMonoidHom) (f_inv := Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨qN.toMonoidHom, hKqN⟩ x
  have hr : Continuous r₀ := by
    apply (Topology.IsQuotientMap.of_surjective_continuous
      hf f.continuous_toFun).continuous_iff.2
    change Continuous (r₀.comp f.toMonoidHom)
    rw [hcomp]
    exact qN.continuous_toFun
  let r : Q →ₜ* S ⧸ N := ⟨r₀, hr⟩
  let H : OpenNormalSubgroup Q := ProCGroups.ProC.OpenNormalSubgroup.ker r
  let P : Subgroup G := (H : Subgroup Q).comap f.toMonoidHom
  have hq_mem_N : ∀ x : P, q x.1 ∈ N := by
    intro x
    have hrf : r (f x.1) = 1 :=
      (ProCGroups.ProC.OpenNormalSubgroup.mem_ker (f := r)).1 x.2
    have hqNx : qN x.1 = 1 :=
      (DFunLike.congr_fun hcomp x.1).symm.trans hrf
    exact (QuotientGroup.eq_one_iff (N := N) (q x.1)).1 hqNx
  let qP : P →ₜ* N :=
    { toMonoidHom := (q.toMonoidHom.comp P.subtype).codRestrict N hq_mem_N
      continuous_toFun :=
        (q.continuous_toFun.comp continuous_subtype_val).subtype_mk hq_mem_N }
  have hNderived : topDerivedTop N 1 = ⊤ := by
    apply top_unique
    intro n _
    rcases n.2 with ⟨k, hkK, hkq⟩
    have hkP : k ∈ P := by
      change f k ∈ (H : Subgroup Q)
      have hfk : f k = 1 := MonoidHom.mem_ker.mp hkK
      rw [hfk]
      exact (H : Subgroup Q).one_mem
    let x : P := ⟨k, hkP⟩
    have hxker :
        x ∈ (ProCGroups.ContinuousMonoidHom.restrictPreimage f (H : Subgroup Q)).ker := by
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact MonoidHom.mem_ker.mp hkK
    have hxder : x ∈ topDerivedTop P 1 :=
      restrictPreimage_ker_le_topDerived_one hAb H hxker
    have hqPx : qP x ∈ topDerivedTop N 1 :=
      topDerived_map_le (f := qP) 1 ⟨x, hxder, rfl⟩
    have hqPx_eq : qP x = n := Subtype.ext hkq
    exact hqPx_eq ▸ hqPx
  apply Group.isPerfect_def.mpr
  rw [topDerivedTop_one_eq_topologicalCommutator,
    topologicalCommutator_eq_commutator_of_isClosed N (isClosed_discrete _)] at hNderived
  exact hNderived

/-- 局所アーベル化の単射性から、核自身の位相についての完全性を導く。 -/
theorem kernel_topologicallyPerfect_of_openNormalAbelianizationInjective
    {G Q : Type u}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [T2Space Q]
    (f : G →ₜ* Q) (hf : Function.Surjective f)
    (hAb : OpenNormalAbelianizationInjective f) :
    (commutator f.ker).topologicalClosure = ⊤ := by
  let K : Subgroup G := f.ker
  have hKclosed : IsClosed (K : Set G) := by
    change IsClosed (f ⁻¹' ({1} : Set Q))
    exact isClosed_singleton.preimage f.continuous_toFun
  let : CompactSpace K := hKclosed.isClosedEmbedding_subtypeVal.compactSpace
  let C : Subgroup K := (commutator K).topologicalClosure
  let T : Set G := K.subtype '' (C : Set K)
  have hTclosed : IsClosed T :=
    ((Subgroup.isClosed_topologicalClosure (commutator K)).isCompact.image
      continuous_subtype_val).isClosed
  apply top_unique
  intro k _
  have hkT : (k : G) ∈ T := by
    apply (ProCGroups.mem_closed_iff_forall_openNormal_quotient hTclosed).2
    intro U
    let : DiscreteTopology (G ⧸ (U : Subgroup G)) :=
      QuotientGroup.discreteTopology U.isOpen'
    let q : G →ₜ* G ⧸ (U : Subgroup G) :=
      ProCGroups.ProC.OpenNormalSubgroup.quotientProj U
    let N : Subgroup (G ⧸ (U : Subgroup G)) := K.map q.toMonoidHom
    have hNperfect : Group.IsPerfect N :=
      isPerfect_kernel_image_of_openNormalAbelianizationInjective f hf hAb q
        (ProCGroups.ProC.OpenNormalSubgroup.quotientProj_surjective U)
    let qK : K →* N :=
      (q.toMonoidHom.comp K.subtype).codRestrict N (fun a => ⟨a, a.2, rfl⟩)
    have hqK : Function.Surjective qK := by
      rintro ⟨s, a, ha, has⟩
      exact ⟨⟨a, ha⟩, Subtype.ext has⟩
    have hmap : (commutator K).map qK = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective qK hqK]
      exact Group.isPerfect_def.mp hNperfect
    have hqk : qK k ∈ (commutator K).map qK := by
      rw [hmap]
      exact Subgroup.mem_top (qK k)
    rcases hqk with ⟨a, ha, haq⟩
    refine ⟨a, ⟨a, Subgroup.le_topologicalClosure (commutator K) ha, rfl⟩, ?_⟩
    exact congrArg Subtype.val haq
  rcases hkT with ⟨a, ha, hak⟩
  have hak' : a = k := Subtype.ext hak
  exact hak' ▸ ha

end Yamaguchi26SolvableCoverings
