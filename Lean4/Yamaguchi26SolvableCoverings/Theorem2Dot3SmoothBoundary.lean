/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26SolvableCoverings.Geometry.Boundary
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.SmoothConnectedCovers
import SchemeTheory.Divisors.SmoothIrreducibleComponents
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Remark 2.3 — 滑らかな境界成分から一般ファイバーの幾何的整性を得る

原稿：`SolvableCoverings.tex`、`rem:smooth-boundary`。
対応する Lean 宣言は `smooth_boundary_2_3`。一つの remark に含まれる一般論と
境界条件への適用を、一つの宣言の二つの結論として記述する。

第一の主張では、スキーム `E` の構造射 `E ⟶ Spec ℤ` が滑らか・有限型・全射であり、
`E` の `ℚ` 上の一般ファイバーが幾何的連結であると仮定する。
結論は、任意の有限 étale 被覆 `T ⟶ E` の任意の既約成分に被約構造を入れると、
その `ℚ` 上の一般ファイバーが幾何的整になること。被覆 `T` の連結性は仮定しない。

第二の主張は、定義 2.2 の条件 `(†)` の第三条件に対する十分条件である。
連結な局所 Noether スキーム `X` 上の水平な有効 Cartier 因子 `D` について、
各被約素成分 `E` の構造射が滑らか・有限型・全射であり、一般ファイバーが
幾何的連結であると仮定する。このとき、任意の連結有限 étale 被覆 `Y ⟶ X` の後で、
`D ×_X Y` の各被約素成分の一般ファイバーが幾何的整になる。
この結論は `(†)` の第三条件であり、`X` の `D` 上での正則性や剰余標数 `2` の
normal crossings 点の存在までは主張しない。

## Lean での表現

`toIntegers E` は `Spec ℤ` への標準構造射である。有限型性は mathlib の表現に従い、
`LocallyOfFiniteType` と `QuasiCompact` の両方で指定する。
`GeometricallyConnected` と `GeometricallyIntegral` は、構造射の
`fiberToSpecResidueField (genericPoint (Spec ℤ))` に適用する。
このファイバーの底体は `Spec ℤ` の一般点の剰余体、すなわち `ℚ` である。

第一の結論の `T.left.reducedIrreducibleComponentι Z hZ` は、既約成分 `Z` に
被約構造を入れたスキームから `T` への包含であり、これに被覆射と `toIntegers E` を
合成して成分の構造射を作る。第二の仮定の `D.1.componentToBase ... Z hZ` も同様に
被約素成分の構造射である。第二の結論
`HasGeometricallyIntegralGenericComponentsAfterCovers D` は、Galois 被覆に限定せず、
すべての連結有限 étale 被覆の後の幾何的整性を要求する。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.FiniteEtale

namespace Yamaguchi26SolvableCoverings

/-- Remark 2.3 (`rem:smooth-boundary`)：`Spec ℤ` 上で滑らか・有限型・全射かつ
一般ファイバーが幾何的連結なスキームの有限 étale 被覆は、各被約既約成分の
一般ファイバーが幾何的整である。これを境界の各素成分に仮定すれば、条件 `(†)` の
第三条件である全連結有限 étale 被覆後の一般成分の幾何的整性が従う。 -/
theorem smooth_boundary_2_3 :
    (∀ (E : Scheme.{0}),
      Smooth (toIntegers E) →
      LocallyOfFiniteType (toIntegers E) →
      QuasiCompact (toIntegers E) →
      Surjective (toIntegers E) →
      GeometricallyConnected
        ((toIntegers E).fiberToSpecResidueField
          (genericPoint (Spec (CommRingCat.of ℤ)))) →
      ∀ (T : FiniteEtale E) (Z : Set T.left)
        (hZ : Z ∈ irreducibleComponents T.left),
        GeometricallyIntegral
          ((T.left.reducedIrreducibleComponentι Z hZ ≫ T.hom ≫ toIntegers E).fiberToSpecResidueField
            (genericPoint (Spec (CommRingCat.of ℤ))))) ∧
    (∀ (X : Scheme.{0}) [ConnectedSpace X] [IsLocallyNoetherian X]
      (D : X.EffectiveCartierDivisor),
      IsHorizontal D →
      (∀ (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme),
        Smooth (D.1.componentToBase (toIntegers X) Z hZ) ∧
        LocallyOfFiniteType (D.1.componentToBase (toIntegers X) Z hZ) ∧
        QuasiCompact (D.1.componentToBase (toIntegers X) Z hZ) ∧
        Surjective (D.1.componentToBase (toIntegers X) Z hZ) ∧
        GeometricallyConnected
          ((D.1.componentToBase (toIntegers X) Z hZ).fiberToSpecResidueField
            (genericPoint (Spec (CommRingCat.of ℤ))))) →
      HasGeometricallyIntegralGenericComponentsAfterCovers D) := by
  let : IsDomain Γ(Spec (CommRingCat.of ℤ), ⊤) :=
    Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv.injective
  let : IsIntegrallyClosed Γ(Spec (CommRingCat.of ℤ), ⊤) :=
    IsIntegrallyClosed.of_equiv
      (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  constructor
  · intro E hsm _ hqc hsurj hgc T Z hZ
    let : Smooth (toIntegers E) := hsm
    let : QuasiCompact (toIntegers E) := hqc
    let : Surjective (toIntegers E) := hsurj
    let : GeometricallyConnected
        ((toIntegers E).fiberToSpecResidueField
          (genericPoint (Spec (CommRingCat.of ℤ)))) := hgc
    let i : T.left.reducedIrreducibleComponent Z hZ ⟶ T.left :=
      T.left.reducedIrreducibleComponentι Z hZ
    let : IsFiniteEtale i :=
      Scheme.reducedIrreducibleComponentι_isFiniteEtale_of_smooth
        (T.hom ≫ toIntegers E) Z hZ
    let C : FiniteEtale E := FiniteEtale.mk (i ≫ T.hom)
    let : ConnectedSpace C.left := inferInstanceAs
      (ConnectedSpace (T.left.reducedIrreducibleComponent Z hZ))
    have hcomp : C.hom ≫ toIntegers E =
        T.left.reducedIrreducibleComponentι Z hZ ≫ T.hom ≫ toIntegers E :=
      Category.assoc _ _ _
    have hgi :=
      (open _root_.EtaleFundamentalGroups in
        geometricallyIntegral_genericFiber_of_connected_finiteEtale_over_smooth_integers
          (toIntegers E) C)
    rw [hcomp] at hgi
    exact hgi
  · intro X _ _ D _ hD Y _ Z hZ
    obtain ⟨W, hW, himage⟩ :=
      D.1.exists_irreducibleComponent_image_comapSubschemeTo_eq Y.hom Z hZ
    obtain ⟨hsm, _, hqc, hsurj, hgc⟩ := hD W hW
    let E : Scheme := D.1.subscheme.reducedIrreducibleComponent W hW
    let p : E ⟶ Spec (CommRingCat.of ℤ) :=
      D.1.componentToBase (toIntegers X) W hW
    let : Smooth p := hsm
    let : QuasiCompact p := hqc
    let : Surjective p := hsurj
    let : GeometricallyConnected
        (p.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of ℤ)))) := hgc
    let f : (D.1.comap Y.hom).subscheme ⟶ D.1.subscheme := D.1.comapSubschemeTo Y.hom
    let c : (D.1.comap Y.hom).subscheme.reducedIrreducibleComponent Z hZ ⟶ E :=
      (D.1.comap Y.hom).subscheme.reducedIrreducibleComponentMap f Z hZ W hW himage
    let : Smooth (D.1.subscheme.reducedIrreducibleComponentι W hW ≫
        D.1.subschemeι ≫ toIntegers X) := hsm
    let : IsFiniteEtale c :=
      Scheme.reducedIrreducibleComponentMap_isFiniteEtale_of_smooth
        f (D.1.subschemeι ≫ toIntegers X) Z hZ W hW himage
    let C : FiniteEtale E := FiniteEtale.mk c
    let : ConnectedSpace C.left := inferInstanceAs
      (ConnectedSpace ((D.1.comap Y.hom).subscheme.reducedIrreducibleComponent Z hZ))
    have hbase : (D.1.comap Y.hom).componentToBase (toIntegers Y.left) Z hZ = c ≫ p := by
      rw [show toIntegers Y.left = Y.hom ≫ toIntegers X from specZIsTerminal.hom_ext _ _]
      exact D.1.componentToBase_comap_eq Y.hom (toIntegers X) Z hZ W hW himage
    change GeometricallyIntegral
      (((D.1.comap Y.hom).componentToBase (toIntegers Y.left) Z hZ).fiberToSpecResidueField
        (genericPoint (Spec (CommRingCat.of ℤ))))
    rw [hbase]
    exact (open _root_.EtaleFundamentalGroups in
      geometricallyIntegral_genericFiber_of_connected_finiteEtale_over_smooth_integers p C)

end Yamaguchi26SolvableCoverings
