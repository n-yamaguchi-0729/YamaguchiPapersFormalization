/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.BoundaryStrictExtension
import EtaleFundamentalGroups.GeometricFiber.RegularBoundarySurjective

/-!
# 補題 1.1：境界の惰性群による基本群の核の記述

原稿：`SolvableCoverings.tex`、Lemma 1.1（`lem:boundary-quotient`）。

## 仮定と結論

`X` は連結な局所 Noether スキーム、`D` は `X` 上の有効 Cartier 因子、
`U = X ∖ Supp(D)` とする。`D` の台の各点で `X` が正則であることを仮定する。
この補題では `D` の水平性は仮定しない。`X` 全体の正則性・整性・正規性も
追加していない。

結論は、`U` が連結で、包含 `U ⟶ X` による étale 基本群の準同型が全射であり、
その核が `D` の各素成分 `E` に付随する惰性群 `I_E` が生成する閉正規部分群に
一致する、というものである。

## Lean での表現

`∃ hU : ConnectedSpace ...` で連結性を得た後、その証拠を型クラスとして設定する。
任意の分離閉体 `Ω` と幾何点 `ξ : Spec Ω ⟶ U` を量化し、
`fundamentalGroupHom U.ι ξ` により同じ幾何点を `X` に合成して得る準同型を使う。

核の右辺 `boundaryStrictInertiaClosure D hreg ξ` は、各境界成分の実際の
strict henselization の分数体の基本群の像を、幾何学的な経路で同じ基点に移し、
閉正規生成した部分群である。

有限 Galois 商がこれらの像を消すと、その被覆の正規化は各成分の局所環上で
étale となる。純性と有限表示による降下で被覆を `X` 全体へ延長し、基本群の核を
有限 Galois 商で判定することで逆の包含を得る。

後続の有限被覆の議論で使う `boundary_quotient_finite_cover` は、正規化上の
幾何点の固定部分群が自明な被覆による、同じ核の別の表示である。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [ConnectedSpace X] [IsLocallyNoetherian X]

/-- 正規化上の有限惰性群が自明な被覆による、補題 1.1 の核の別表示。
境界上で正則なら、その補集合は連結であり、基本群の写像は全射となる。
その核を、全ての境界惰性群を消す有限 Galois 商の核の共通部分として記述する。 -/
theorem boundary_quotient_finite_cover
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) :
    ∃ hU : ConnectedSpace D.1.supportComplement,
      letI : ConnectedSpace D.1.supportComplement := hU
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement),
        Function.Surjective (fundamentalGroupHom D.1.supportComplement.ι point) ∧
          (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker =
            boundaryUnramifiedKernelIntersection D point := by
  let hU : ConnectedSpace D.1.supportComplement :=
    boundaryComplement_connectedSpace D hreg
  refine ⟨hU, ?_⟩
  let : ConnectedSpace D.1.supportComplement := hU
  intro Ω _ _ point
  refine ⟨boundaryComplement_fundamentalGroupHom_surjective D hreg point, ?_⟩
  exact le_antisymm
    (kernel_le_boundaryUnramifiedKernelIntersection D hreg point)
    (boundaryUnramifiedKernelIntersection_le_kernel D hreg point)

/-- 補題 1.1（`lem:boundary-quotient`）。境界上で正則なら補集合は連結であり、
基本群の写像は全射となる。その核は各素成分の厳密局所惰性群の閉正規生成に等しい。 -/
theorem boundary_quotient_1_1
    (D : X.EffectiveCartierDivisor) (hreg : D.IsAmbientRegularAlongSupport) :
    ∃ hU : ConnectedSpace D.1.supportComplement,
      letI : ConnectedSpace D.1.supportComplement := hU
      ∀ (Ω : Type) [Field Ω] [IsSepClosed Ω]
        (point : Spec (CommRingCat.of Ω) ⟶ D.1.supportComplement),
        Function.Surjective (fundamentalGroupHom D.1.supportComplement.ι point) ∧
          (fundamentalGroupHom D.1.supportComplement.ι point).toMonoidHom.ker =
            boundaryStrictInertiaClosure D hreg point := by
  let hU : ConnectedSpace D.1.supportComplement :=
    boundaryComplement_connectedSpace D hreg
  refine ⟨hU, ?_⟩
  let : ConnectedSpace D.1.supportComplement := hU
  intro Ω _ _ point
  refine ⟨boundaryComplement_fundamentalGroupHom_surjective D hreg point, ?_⟩
  exact le_antisymm
    (kernel_le_boundaryStrictInertiaClosure D hreg point)
    (boundaryStrictInertiaClosure_le_kernel D hreg point)

end Yamaguchi26SolvableCoverings
