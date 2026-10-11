/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.BoundaryCyclotomic
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot1BoundaryQuotient
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot2InertiaControl
import Nyll.EtaleFundamentalGroups.GaloisCategories.DiscreteCharacters
import Nyll.ProCGroups.Abelian.CharacterDetection
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# 補題 2.1：境界を除いても基本群のアーベル化は変わらない

Source: [Yamaguchi, arXiv:2610.02948v1](https://arxiv.org/abs/2610.02948v1), Lemma 2.1.
対応する Lean 宣言は `abelian_invariance_2_1`。

`X` を連結な局所 Noether スキーム、`D` を水平な有効 Cartier 因子とし、
`U = X \ Supp(D)` と置く。次の三条件を仮定する。

* `X` は `D` の台の各点で正則である。
* `D` の各素成分は、剰余標数が `2` で、`D` 全体が normal crossings となる点を含む。
* `D` の各素成分に被約構造を入れたとき、その `ℚ` 上の一般ファイバーは幾何的整である。

結論は、`U` が連結であり、包含 `j : U ⟶ X` が誘導する準同型
`f : π₁ᵉᵗ(U, ξ) → π₁ᵉᵗ(X, j(ξ))` が、両辺の位相的アーベル化の同型を誘導すること。
任意の分離閉体 `Ω` と幾何学的基点 `ξ : Spec Ω ⟶ U` について述べている。

Lean では `D.1.supportComplement` が `U`、その `.ι` が `j` を表す。
`IsHorizontal D` は各素成分が `Spec ℤ` を支配するという意味である。
`HasGeometricallyIntegralGenericComponents D.1` は上記の一般ファイバーの条件であり、
この補題では有限 étale 被覆の後の条件までは要求しない。
定理文に位相群同型 `e : Gᵃᵇ ≃ Hᵃᵇ` の存在と、
商写像 `q_G`, `q_H` に対する等式 `e(q_G(g)) = q_H(f(g))` を要求する。
したがって、結論の同型は包含から誘導される写像と一致する。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace Yamaguchi26SolvableCoverings

universe v

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- A finite cover whose deck group embeds into an abelian group has trivial
boundary stabilizers under the arithmetic hypotheses. Cyclotomic inversion
makes each character value have order dividing two, while Theorem 1.2 gives
an odd order from the actual stabilizer subgroup. -/
private theorem isBoundaryUnramified_of_abelian_embedding
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport)
    (hnc : D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent 2)
    (hgeom : HasGeometricallyIntegralGenericComponents D.1) :
    let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
    ∀ (W : FiniteEtale D.1.supportComplement) (_hW : IsGalois W)
      {A : Type v} [CommGroup A] (e : (Aut W)ᵐᵒᵖ →* A),
      Function.Injective e → IsBoundaryUnramified D W := by
  intro hConnected
  let : ConnectedSpace D.1.supportComplement := hConnected
  intro W hW A _ e he E z hz
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro σ hσ
  let s : finiteCoverInertia D W E z := ⟨σ, hσ⟩
  have hodd : ¬ 2 ∣ Nat.card (finiteCoverInertia D W E z) :=
    finite_inertia_control D hhor hreg E 2 Nat.prime_two (hnc E.val E.property) W hW z hz
  have hinv : e (MulOpposite.op σ) = (e (MulOpposite.op σ))⁻¹ := by
    have h := e.map_isConj (finiteCoverInertia_isConj_inv D hhor hreg hgeom W hW E z hz s)
    simpa only [map_inv] using isConj_iff_eq.mp h
  have htwo : (e (MulOpposite.op σ)) ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun t => e (MulOpposite.op σ) * t) hinv).trans (mul_inv_cancel _)
  have hcard : (e (MulOpposite.op σ)) ^ Nat.card (finiteCoverInertia D W E z) = 1 := by
    have h := congrArg (fun t : finiteCoverInertia D W E z => e (MulOpposite.op (t : Aut W)))
      (pow_card_eq_one' (x := s))
    simpa only [Subgroup.coe_pow, MulOpposite.op_pow, map_pow,
      Subgroup.coe_one, MulOpposite.op_one, map_one] using h
  have hone : e (MulOpposite.op σ) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.prime_two.coprime_iff_not_dvd.mpr hodd)
      (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hcard))
  exact MulOpposite.op_injective (he (hone.trans (map_one e).symm))

/-- 補題 2.1：三つの境界条件の下で、補集合は連結であり、
包含は基本群の位相的アーベル化の同型を誘導する。 -/
theorem abelian_invariance_2_1
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport)
    (hnc : D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent 2)
    (hgeom : HasGeometricallyIntegralGenericComponents D.1) :
    ConnectedSpace D.1.supportComplement ∧
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement),
        ∃ e : TopologicalAbelianization π₁ᵉᵗ(point) ≃ₜ*
            TopologicalAbelianization π₁ᵉᵗ(point ≫ D.1.supportComplement.ι),
          ∀ g : π₁ᵉᵗ(point), e (QuotientGroup.mk g) =
            QuotientGroup.mk (fundamentalGroupHom D.1.supportComplement.ι point g) := by
  let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
  refine ⟨inferInstance, ?_⟩
  intro Ω _ _ point
  let f := fundamentalGroupHom D.1.supportComplement.ι point
  have hf : Function.Surjective f :=
    boundaryComplement_fundamentalGroupHom_surjective D hreg point
  have hker : f.toMonoidHom.ker = boundaryUnramifiedKernelIntersection D point :=
    ((boundary_quotient_finite_cover D hreg).choose_spec Ω point).2
  have hkill : f.toMonoidHom.ker ≤ Subgroup.closedCommutator π₁ᵉᵗ(point) := by
    intro g hg
    apply ProCGroups.Abelian.TopologicalAbelianization.mk_eq_one_iff.mp
    have hclasses : ProCGroups.Abelian.TopologicalAbelianization.mk π₁ᵉᵗ(point) g =
        ProCGroups.Abelian.TopologicalAbelianization.mk π₁ᵉᵗ(point) 1 := by
      apply ProCGroups.Abelian.TopologicalAbelianization.mk_eq_iff_finite_characters_eq.mpr
      intro A _ _ _ _ chi
      obtain ⟨W, hW, w, e, he, hchi⟩ :=
        exists_galoisObject_discreteCharacter_embedding (fiber point) chi
      have hU : IsBoundaryUnramified D W :=
        isBoundaryUnramified_of_abelian_embedding D hhor hreg hnc hgeom W hW e he
      have hgI : g ∈ boundaryUnramifiedKernelIntersection D point := hker ▸ hg
      have hgq : (let : IsGalois W := hW
          galoisObjectQuotientMonoidHom (fiber point) π₁ᵉᵗ(point) W w) g = 1 :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp
          (Subgroup.mem_iInf.mp hgI W) hW) w) hU
      calc
        chi g = e ((let : IsGalois W := hW
            galoisObjectQuotientMonoidHom (fiber point) π₁ᵉᵗ(point) W w) g) :=
          (DFunLike.congr_fun hchi g).symm
        _ = e 1 := congrArg e hgq
        _ = 1 := map_one e
        _ = chi 1 := (map_one chi).symm
    exact hclasses.trans (map_one _)
  have hinj :=
    (ProCGroups.Abelian.TopologicalAbelianization.injective_map_iff_ker_le_closedCommutator f
        hf).mpr hkill
  have hsurj := ProCGroups.Abelian.TopologicalAbelianization.surjective_map_of_surjective f hf
  let e := MulEquiv.ofBijective
    (ProCGroups.Abelian.TopologicalAbelianization.map f).toMonoidHom ⟨hinj, hsurj⟩
  have he : Continuous e := (ProCGroups.Abelian.TopologicalAbelianization.map f).continuous
  refine ⟨{ toMulEquiv := e
            continuous_toFun := he
            continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
              (f := e.toEquiv) he }, ?_⟩
  intro g
  exact ProCGroups.Abelian.TopologicalAbelianization.map_apply_mk f g

end Yamaguchi26SolvableCoverings
