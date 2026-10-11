/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.Boundary
import Nyll.EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# 境界の惰性群：正規化の幾何点固定部分群とライブラリの比較

ここでは実際の有限 étale 被覆を相対正規化し、その上の幾何点を固定する被覆自己同型の
部分群を定義する。位相的な点を固定する分解群とは異なり、幾何点からの射の等式を
要求する。自己同型の延長と群公理は正規化の普遍性から証明する。
台のスキーム全体の整性・正規性は仮定しない。

原稿の惰性群は、境界成分一般点の strict henselization の分数体の基本群の像である。
`BoundaryStrictInertia` が共通の基点でその閉正規生成を定義する。
有限被覆の議論に使う固定部分群と、その幾何学的な比較は次の実装に分けている。

* EFG `Inertia.AffineGeometricPoint` はアフィン幾何点の固定条件を、
  その座標環の準同型の核に付随するイデアル惰性群と比較する。
* EFG `Inertia.AffineNormalizationGeometricPoint` は、
  `normalizationDesc` と整閉包への自己同型の制限の可換性を証明し、
  アフィン相対正規化の実際の幾何点固定部分群とイデアル惰性群を同定する。
* EFG `Inertia.NormalizationBaseChange` は正規化と基底変換の比較射が
  自己準同型と可換であることを証明する。smooth・étale 基底変換では
  その比較同型を用いて対応する点を構成し、固定条件の同値を得る。
* EFG `StrictHenselian.GeometricStalk*` は幾何点付き étale 近傍の余極限として
  環を構成し、局所環性・Hensel性・剰余体の分離閉性を証明する。
  `GeometricStalkResidueClosure` は選んだ分離閉包との剰余体の同型を与える。
* EFG `Inertia.ClosedNormalGeneration` は、閉正規生成部分群と
  それを消す有限 Galois 商の核の共通部分との群論的比較を証明する。

`BoundaryStrictImage` は実際の厳密局所像が固定する正規化上の点を構成する。
`BoundaryStrictExtension` は厳密局所作用の自明性から被覆を大域的に延長する。
1.2では、実際に構成した局所化被覆の成分と素イデアルを用いて
EFG `Kummer.NormalCrossings.ComponentMappedFiniteQuotientInertia` の素数非整除を適用し、
厳密局所像への包含によって原稿の結論を得る。
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace Yamaguchi26SolvableCoverings

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- The geometric point over the generic point of a reduced boundary component. -/
def componentGeometricPoint (D : X.EffectiveCartierDivisor) (E : Component D) :
    Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (X.residueField (componentPoint D E))
      (AlgebraicClosure (X.residueField (componentPoint D E))))) ≫
    X.fromSpecResidueField (componentPoint D E)

/-- A deck transformation extends canonically to the relative normalization
of the finite cover over the ambient scheme. -/
def normalizationDeck (D : X.EffectiveCartierDivisor)
    (W : FiniteEtale D.1.supportComplement) (σ : Aut W) :
    (W.hom ≫ D.1.supportComplement.ι).normalization ⟶
      (W.hom ≫ D.1.supportComplement.ι).normalization :=
  (W.hom ≫ D.1.supportComplement.ι).normalizationDesc
    (σ.hom.left ≫ (W.hom ≫ D.1.supportComplement.ι).toNormalization)
    (W.hom ≫ D.1.supportComplement.ι).fromNormalization (by
      rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
      have hw : σ.hom.left ≫ W.hom = W.hom := σ.hom.w
      rw [← Category.assoc, hw])

/-- Extending the identity deck transformation gives the identity on the
relative normalization, by uniqueness in its universal property. -/
private theorem normalizationDeck_one (D : X.EffectiveCartierDivisor)
    (W : FiniteEtale D.1.supportComplement) :
    normalizationDeck D W 1 =
      𝟙 (W.hom ≫ D.1.supportComplement.ι).normalization := by
  refine Scheme.Hom.normalization.hom_ext (W.hom ≫ D.1.supportComplement.ι)
    _ _ (W.hom ≫ D.1.supportComplement.ι).fromNormalization ?_ ?_ ?_
  · rw [normalizationDeck, Scheme.Hom.toNormalization_normalizationDesc]
    change (𝟙 W.left) ≫ (W.hom ≫ D.1.supportComplement.ι).toNormalization =
      (W.hom ≫ D.1.supportComplement.ι).toNormalization ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · exact Scheme.Hom.normalizationDesc_comp _ _ _ _
  · exact Category.id_comp _

/-- Extending a product agrees with composing the extensions. Multiplication
in `Aut W` reverses the order of categorical composition. -/
private theorem normalizationDeck_mul (D : X.EffectiveCartierDivisor)
    (W : FiniteEtale D.1.supportComplement) (σ τ : Aut W) :
    normalizationDeck D W (σ * τ) =
      normalizationDeck D W τ ≫ normalizationDeck D W σ := by
  refine Scheme.Hom.normalization.hom_ext (W.hom ≫ D.1.supportComplement.ι)
    _ _ (W.hom ≫ D.1.supportComplement.ι).fromNormalization ?_ ?_ ?_
  · simp only [normalizationDeck, Scheme.Hom.toNormalization_normalizationDesc,
      Scheme.Hom.toNormalization_normalizationDesc_assoc, Aut.Aut_mul_def,
      Category.assoc]
    rfl
  · exact Scheme.Hom.normalizationDesc_comp _ _ _ _
  · simp only [normalizationDeck, Category.assoc, Scheme.Hom.normalizationDesc_comp]

/-- The finite-cover inertia subgroup is the stabilizer of an actual geometric
point of the normalization. The condition that the point lies above the
chosen boundary component is supplied separately, by its displayed equation. -/
def finiteCoverInertia (D : X.EffectiveCartierDivisor)
    (W : FiniteEtale D.1.supportComplement) (E : Component D)
    (z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
      (W.hom ≫ D.1.supportComplement.ι).normalization) : Subgroup (Aut W) where
  carrier := {σ | z ≫ normalizationDeck D W σ = z}
  one_mem' := by
    change z ≫ normalizationDeck D W 1 = z
    rw [normalizationDeck_one, Category.comp_id]
  mul_mem' := by
    intro σ τ hσ hτ
    change z ≫ normalizationDeck D W σ = z at hσ
    change z ≫ normalizationDeck D W τ = z at hτ
    change z ≫ normalizationDeck D W (σ * τ) = z
    rw [normalizationDeck_mul, ← Category.assoc, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    change z ≫ normalizationDeck D W σ = z at hσ
    change z ≫ normalizationDeck D W σ⁻¹ = z
    calc
      z ≫ normalizationDeck D W σ⁻¹ =
          (z ≫ normalizationDeck D W σ) ≫ normalizationDeck D W σ⁻¹ := by rw [hσ]
      _ = z ≫ normalizationDeck D W (σ⁻¹ * σ) := by
        rw [normalizationDeck_mul, Category.assoc]
      _ = z := by rw [inv_mul_cancel, normalizationDeck_one, Category.comp_id]

/-- All generic boundary inertia groups of this finite cover are trivial.
The quantification is over geometric points of the actual normalization,
including every component of the divisor. -/
def IsBoundaryUnramified (D : X.EffectiveCartierDivisor)
    (W : FiniteEtale D.1.supportComplement) : Prop :=
  ∀ (E : Component D)
    (z : Spec (.of (AlgebraicClosure (X.residueField (componentPoint D E)))) ⟶
      (W.hom ≫ D.1.supportComplement.ι).normalization),
    z ≫ (W.hom ≫ D.1.supportComplement.ι).fromNormalization =
        componentGeometricPoint D E →
      finiteCoverInertia D W E z = ⊥

/-- Intersect the kernels of all pointed finite Galois covers whose
normalization stabilizers at the generic boundary points are trivial.
Identifying this subgroup with the closed normal subgroup generated by the
manuscript's strict-henselization inertia groups remains to be formalized. -/
def boundaryUnramifiedKernelIntersection (D : X.EffectiveCartierDivisor)
    [ConnectedSpace D.1.supportComplement]
    {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ D.1.supportComplement) : Subgroup π₁ᵉᵗ(ξ) :=
  ⨅ (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (w : (fiber ξ).obj W) (_h : IsBoundaryUnramified D W),
    (letI : IsGalois W := hW
     galoisObjectQuotientMonoidHom (fiber ξ) π₁ᵉᵗ(ξ) W w).ker

end Yamaguchi26SolvableCoverings
