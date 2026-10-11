/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.BoundaryInertia
import EtaleFundamentalGroups.GeometricFiber.RegularBoundarySurjective

import Yamaguchi26SolvableCoverings.Geometry.BoundaryBranchGeometricPoint
import Yamaguchi26SolvableCoverings.Geometry.BoundaryStrictImage
import EtaleFundamentalGroups.Inertia.BoundaryNormalizationPoint
import EtaleFundamentalGroups.Inertia.GaloisNormalizationPointLift
import EtaleFundamentalGroups.Inertia.FiniteEtaleAwayNormalizationPoint
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverInertia
import SchemeTheory.LocalGeometry.HeightTwo.ResidueCharacteristic
import Mathlib.Algebra.Group.Subgroup.MulOpposite
import Mathlib.GroupTheory.Index
/-!
# 補題 1.2：正規交差点の剰余標数と惰性群の位数

原稿：`SolvableCoverings.tex`、Lemma 1.2（`lem:inertia-control`）。

## 仮定と結論

`X` は連結な局所 Noether スキーム、`D` は水平な有効 Cartier 因子、
`U = X ∖ Supp(D)`、`E` は `D` の素成分、`p` は素数とする。
水平とは各素成分が `Spec ℤ` を支配することである。
次の二条件を仮定する。

* `X` は `D` の台の全ての点で正則である。
* `E` 上に、剰余標数が `p` で、`D` 全体が normal crossings となる点がある。

結論は、任意の連結有限 étale Galois 被覆 `W ⟶ U` に対して、
境界成分 `E` の惰性群 `I_E(W/U)` の位数を `p` が割らない、というものである。
単に `E` 自身がその点で滑らかであるという仮定ではない。また、そのような点は
この補題で選んだ一つの成分 `E` にあればよい。

## Lean での表現

正則境界の補集合の連結性を既証明の一般定理から取り出し、`U` の型クラスとして設定する。
`W : FiniteEtale U` と Galois 対象であるという条件 `IsGalois W` を量化する。

`E` の一般点の剰余体の代数閉包から来る幾何点を
`componentGeometricPoint D E` とし、その点の上にある相対正規化の幾何点 `z` を
全て量化する。表示された合成写像の等式は、`z` が確かにその境界成分の一般点の
上にあることを要求する。`finiteCoverInertia D W E z` は `z` の固定部分群であり、
結論 `¬ p ∣ Nat.card ...` は、この固定部分群の位数を `p` が割らないことを表す。
全ての幾何点の選択に同じ位数の条件を課す。

原稿の惰性群は strict henselization の分数体の基本群の像で定義される。
`inertia_control_1_2` はその実際の有限商への像について結論を証明する。
指定した幾何点の値域を保って正規化上の点を構成し、有限像をその固定部分群に含める。
下の固定部分群についての定理と部分群の位数の整除性から、原稿の素数非整除が従う。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups EtaleFundamentalGroups.Inertia

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- 補題 1.2（`lem:inertia-control`）の固定部分群についての補助定理。
水平境界の成分 `E` に剰余標数 `p` の正規交差点があれば、
任意の連結有限 étale Galois 被覆の `E` における惰性群の位数は `p` と互いに素。 -/
theorem finite_inertia_control
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport) (E : Component D)
    (p : ℕ) (hp : p.Prime)
    (hnc : ∃ x : D.1.subscheme, x ∈ E.val ∧
      ringChar (X.residueField (D.1.subschemeι x)) = p ∧
        D.IsNormalCrossingsAt (D.1.subschemeι x)) :
    letI : ConnectedSpace D.1.supportComplement :=
      boundaryComplement_connectedSpace D hreg
    ∀ (W : FiniteEtale D.1.supportComplement) (_hW : IsGalois W)
      (z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
        (W.hom ≫ D.1.supportComplement.ι).normalization),
      z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization =
          componentGeometricPoint D E →
        ¬ p ∣ Nat.card (finiteCoverInertia D W E z) := by
  let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
  intro W hW z hz
  obtain ⟨U, f, hf, u, q, hq, hmapped, hpoint⟩ :=
    exists_arithmeticBoundaryChart_with_componentGeometricPoint D hhor hreg E p hp hnc
  let : Etale f := hf
  let : q.IsPrime := hq
  obtain ⟨P, hqP, hPheight, r, t, branch, hVdomain, hVregular, hVnormal,
    hboundary, hNC, hbranch, hqV, hCharZero, hpV, _hmapped⟩ := hmapped
  let : P.asIdeal.IsPrime := P.isPrime
  let V := Localization.AtPrime P.asIdeal
  let : IsDomain V := hVdomain
  let : IsRegularRing V := hVregular
  let : IsIntegrallyClosed V := hVnormal
  obtain ⟨y, hyideal, hy⟩ := hpoint P.asIdeal P.isPrime hqP.le
  have hzy : z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization =
      y ≫ Scheme.localizationAtPrimeTo U u P.asIdeal ≫ f := by
    exact hz.trans (by simpa only [Scheme.localizationAtPrimeTo, Category.assoc] using hy.symm)
  obtain ⟨qA, hqA, hfixA⟩ :=
    exists_boundaryAway_normalizationPoint D.1 f u P t hboundary W z y hzy
  let b := boundaryProduct t r
  have hb : b ≠ 0 := Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
  let Away := Localization.Away b
  let : IsDomain Away := IsLocalization.Away.isDomain Away hb
  let : IsIntegrallyClosed Away := isIntegrallyClosed_of_isLocalization Away
    (Submonoid.powers b)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hb))
  let c := D.1.boundaryAwayToSupportComplement f u P t hboundary
  let a : Spec (.of Away) ⟶ Spec (.of V) :=
    Spec.map (CommRingCat.ofHom (algebraMap V Away))
  let s := genericPoint (Spec (.of Away))
  let Ω := AlgebraicClosure ((Spec (.of Away)).residueField s)
  let xi : Spec (.of Ω) ⟶ Spec (.of Away) :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of Away)).residueField s) Ω)) ≫
      (Spec (.of Away)).fromSpecResidueField s
  obtain ⟨Z, i, qZ, zZ, w, hi, hZ, hiz, hqZ, hlift⟩ :=
    exists_galoisComponent_normalizationPoint_fixed_lift c xi W hW a qA
  let : Mono i := hi
  let : IsGalois Z := hZ
  let : IsIntegral Z.left := isIntegral_left_of_isConnected_finiteEtale Z
  let K := (Spec (.of Away)).functionField
  let L := Z.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
  let : Algebra V K := localizationAwaySpecFunctionFieldAlgebra b hb
  let : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra b hb Z
  let : IsScalarTower V K L := finiteEtaleAway_functionField_isScalarTower b hb Z
  let : IsFractionRing V K := localizationAwaySpecFunctionField_isFractionRing b hb
  let : FiniteDimensional K L := finiteDimensional_functionField_of_finiteEtale_isConnected Z
  let : _root_.IsGalois K L := isGalois_functionField_of_isGalois_finiteEtale Z hZ
  obtain ⟨φ, hφbase, hφfix⟩ := exists_finiteEtaleAway_normalizationPoint_inertia_iff V b hb Z qZ
  let Q := RingHom.ker φ
  have hQprime : Q.IsPrime := RingHom.ker_isPrime φ
  have hQbranch : Q.LiesOver (Ideal.span ({t branch} : Set V)) := by
    have h := ker_liesOver_of_specMap_comp φ y (hφbase.trans (hqZ.trans hqA))
    simpa only [hyideal, hqV] using h
  let φV : (V ⧸ Ideal.span ({t branch} : Set V)) →+* (V ⧸ IsLocalRing.maximalIdeal V) :=
    (localizationAtPrimeBranchQuotientToResidue q P.asIdeal hqP.le).comp
      (Ideal.quotEquivOfEq hqV.symm).toRingHom
  have hcoprime :=
      Kummer.splitStrictNormalCrossings_finiteEtaleGaloisCover_normalizationInertia_coprime
    (A := V) (k := V ⧸ IsLocalRing.maximalIdeal V)
    hNC branch hbranch hCharZero Z hZ Q hQprime hQbranch φV p hpV hp
  let J := Q.inertia Gal(L/K)
  let e : (Aut Z)ᵐᵒᵖ ≃* Gal(L/K) := finiteEtaleAutOpFunctionFieldMulEquiv Z hZ
  let μ : Gal(L/K) →* (Aut W)ᵐᵒᵖ :=
    (FiniteEtale.galoisPullbackComponentQuotientMonoidHom c xi W hW w Z i zZ hiz hZ hi).comp
      e.symm.toMonoidHom
  have hincl : (finiteCoverInertia D W E z).op ≤ J.map μ := by
    intro σ hσ
    have hσfixed : z ≫ normalizationEndomorphism (W.hom ≫ D.1.supportComplement.ι)
        σ.unop.hom.left (by
          rw [← Category.assoc]
          exact congrArg (fun k => k ≫ D.1.supportComplement.ι) σ.unop.hom.w) = z := hσ
    obtain ⟨τ, hτimage, hτfixed⟩ := hlift σ.unop ((hfixA σ.unop).mpr hσfixed)
    refine ⟨finiteEtaleAutFunctionFieldAlgEquiv Z τ, (hφfix τ).mpr hτfixed, ?_⟩
    change (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
      c xi W hW w Z i zZ hiz hZ hi) (e.symm (e (MulOpposite.op τ))) = σ
    rw [e.symm_apply_apply]
    exact hτimage
  have hdvd : Nat.card (finiteCoverInertia D W E z) ∣ Nat.card J := by
    rw [Nat.card_congr (finiteCoverInertia D W E z).equivOp]
    exact (Subgroup.card_dvd_of_le hincl).trans (J.card_map_dvd μ)
  exact hp.coprime_iff_not_dvd.mp (hcoprime.of_dvd_left hdvd).symm

/-- 補題 1.2（`lem:inertia-control`）：原稿で定義される strict henselization の
分数体の基本群の実有限像は、指定した素数で割り切れない位数を持つ。 -/
theorem inertia_control_1_2
    (D : X.EffectiveCartierDivisor) (hhor : IsHorizontal D)
    (hreg : D.IsAmbientRegularAlongSupport) (E : Component D)
    (p : ℕ) (hp : p.Prime)
    (hnc : ∃ x : D.1.subscheme, x ∈ E.val ∧
      ringChar (X.residueField (D.1.subschemeι x)) = p ∧
        D.IsNormalCrossingsAt (D.1.subschemeι x))
    {Ξ : Type} [Field Ξ] [IsSepClosed Ξ]
    (xi : Spec (.of Ξ) ⟶ Spec (.of (boundaryStrictFractionField D E))) :
    let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
    ∀ (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ boundaryStrictGenericMorphism D hreg E)).obj W),
      ¬ p ∣ Nat.card
        (finiteEtaleGaloisCoverQuotientOfMorphism
          (boundaryStrictGenericMorphism D hreg E) xi W hW w).range := by
  let : ConnectedSpace D.1.supportComplement := boundaryComplement_connectedSpace D hreg
  intro _ W hW w
  obtain ⟨z, hz, hle⟩ :=
    exists_componentNormalizationPoint_strictImage_le_inertia D hreg E xi W hW w
  have hnot := finite_inertia_control D hhor hreg E p hp hnc W hW z hz
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [← Nat.card_congr (finiteCoverInertia D W E z).equivOp] at hdvd
  exact fun h => hnot (h.trans hdvd)

end Yamaguchi26SolvableCoverings
