/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.Data.Finset.Union
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.SchemeHomDescent
import Mathlib.Data.Fintype.EquivFin

/-!
# Scheme Pair Descent

A morphism from a qcqs constant extension to a locally finitely presented
constant extension descends to one finite coefficient field, with both structure
maps and recovery preserved.
-/

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u v
namespace EtaleFundamentalGroups
variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- A morphism from a qcqs constant extension to a locally finitely presented
constant extension descends to one finite coefficient field, with both structure
maps and recovery preserved. -/
theorem exists_finiteIntermediateField_schemePairHom
    [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (A B : Scheme.{u}) (p : A ⟶ X) (q : B ⟶ X)
    [CompactSpace A] [QuasiSeparatedSpace A] [LocallyOfFinitePresentation q]
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (p ≫ f) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (q ≫ f))
    (haX : a ≫ pullback.snd _ (q ≫ f) ≫ q =
      pullback.snd _ (p ≫ f) ≫ p)
    (haL : a ≫ pullback.fst _ (q ≫ f) = pullback.fst _ (p ≫ f)) :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ g : pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (p ≫ f) ⟶
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (q ≫ f),
        g ≫ pullback.fst _ (q ≫ f) = pullback.fst _ (p ≫ f) ∧
        g ≫ pullback.snd _ (q ≫ f) ≫ q =
          pullback.snd _ (p ≫ f) ≫ p ∧
        (constantFieldInverseLimitCone k L A (p ≫ f)).π.app (op s) ≫ g =
          a ≫ (constantFieldInverseLimitCone k L B (q ≫ f)).π.app (op s) := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let a' : pullback φ (p ≫ f) ⟶ pullback q p :=
    pullback.lift (a ≫ pullback.snd φ (q ≫ f)) (pullback.snd φ (p ≫ f))
      (by simpa only [Category.assoc] using haX)
  obtain ⟨s, hfin, b, hb, hbA⟩ := exists_finiteIntermediateField_schemeHom k L
    A (pullback q p) (p ≫ f) (pullback.snd q p) a'
    (pullback.lift_snd _ _ _)
  let φs := Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))
  let rA : pullback φ (p ≫ f) ⟶ pullback φs (p ≫ f) :=
    (constantFieldInverseLimitCone k L A (p ≫ f)).π.app (op s)
  let rB : pullback φ (q ≫ f) ⟶ pullback φs (q ≫ f) :=
    (constantFieldInverseLimitCone k L B (q ≫ f)).π.app (op s)
  have hrAfst : rA ≫ pullback.fst φs (p ≫ f) = pullback.fst φ (p ≫ f) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.adjoin k (s : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L A (p ≫ f) s
  have hrBfst : rB ≫ pullback.fst φs (q ≫ f) = pullback.fst φ (q ≫ f) ≫
      Spec.map (CommRingCat.ofHom (IntermediateField.adjoin k (s : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L B (q ≫ f) s
  have hrBsnd : rB ≫ pullback.snd φs (q ≫ f) = pullback.snd φ (q ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L B (q ≫ f)).π.app (op s))
  change rA ≫ b = a' at hb
  let b' : pullback φs (p ≫ f) ⟶ B := b ≫ pullback.fst q p
  have hbX : b' ≫ q = pullback.snd φs (p ≫ f) ≫ p := by
    dsimp only [b']
    rw [Category.assoc, pullback.condition, ← Category.assoc, hbA]
  let g : pullback φs (p ≫ f) ⟶ pullback φs (q ≫ f) :=
    pullback.lift (pullback.fst φs (p ≫ f)) b' (by
      rw [← Category.assoc, hbX, Category.assoc]
      exact pullback.condition)
  refine ⟨s, hfin, g, pullback.lift_fst _ _ _, ?_, ?_⟩
  · rw [← Category.assoc, pullback.lift_snd]
    exact hbX
  · change rA ≫ g = a ≫ rB
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, hrBfst,
        ← Category.assoc, haL]
      exact hrAfst
    · rw [Category.assoc, pullback.lift_snd]
      change rA ≫ (b ≫ pullback.fst q p) = _
      rw [← Category.assoc, hb, pullback.lift_fst, Category.assoc, hrBsnd]

private theorem constantFieldSpec_comp
    (s : Finset L) :
    Spec.map (CommRingCat.ofHom (IntermediateField.adjoin k (s : Set L)).val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L)))) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  rw [← Spec.map_comp]
  rfl

/-- Each constant-field cone map is the base change of the literal coefficient inclusion. -/
theorem constantFieldInverseLimitCone_π_app_isPullback
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) (s : Finset L) :
    IsPullback ((constantFieldInverseLimitCone k L X f).π.app (op s))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)
      (pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)
      (Spec.map (CommRingCat.ofHom
        (IntermediateField.adjoin k (s : Set L)).val.toRingHom)) := by
  let p : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f :=
    (constantFieldInverseLimitCone k L X f).π.app (op s)
  change IsPullback p _ _ _
  apply IsPullback.of_right (v₁₃ := f)
    (h₁₂ := pullback.snd (Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f)
    (h₂₂ := Spec.map (CommRingCat.ofHom
      (algebraMap k (IntermediateField.adjoin k (s : Set L)))))
  · have hp : p ≫
        pullback.snd (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L))) f :=
      Over.w ((constantFieldInverseLimitOverCone k L X f).π.app (op s))
    rw [hp, constantFieldSpec_comp]
    exact (IsPullback.of_hasPullback _ _).flip
  · exact constantFieldInverseLimitCone_π_app_fst k L X f s
  · exact (IsPullback.of_hasPullback _ _).flip

/-- A map between constant-field stages that recovers an isomorphism over the
extension field is already an isomorphism, by faithfully flat descent. -/
theorem isIso_of_constantFieldStageHom
    (X Y : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k)) (s : Finset L)
    (a : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) g) [IsIso a]
    (b : pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) f ⟶
      pullback (Spec.map (CommRingCat.ofHom
        (algebraMap k (IntermediateField.adjoin k (s : Set L))))) g)
    (ha : a ≫ pullback.fst _ g = pullback.fst _ f)
    (hb : b ≫ pullback.fst _ g = pullback.fst _ f)
    (hab : (constantFieldInverseLimitCone k L X f).π.app (op s) ≫ b =
      a ≫ (constantFieldInverseLimitCone k L Y g).π.app (op s)) : IsIso b := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φs := Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))
  let ψ := Spec.map (CommRingCat.ofHom
    (IntermediateField.adjoin k (s : Set L)).val.toRingHom)
  let pX : pullback φ f ⟶ pullback φs f :=
    (constantFieldInverseLimitCone k L X f).π.app (op s)
  let pY : pullback φ g ⟶ pullback φs g :=
    (constantFieldInverseLimitCone k L Y g).π.app (op s)
  have hX : IsPullback pX (pullback.fst φ f) (pullback.fst φs f) ψ :=
    constantFieldInverseLimitCone_π_app_isPullback k L X f s
  have hY : IsPullback pY (pullback.fst φ g) (pullback.fst φs g) ψ :=
    constantFieldInverseLimitCone_π_app_isPullback k L Y g s
  have houter : IsPullback (a ≫ pullback.fst φ g) pX ψ
      (b ≫ pullback.fst φs g) := by
    rw [ha, hb]
    exact hX.flip
  have hsquare : IsPullback a pX pY b :=
    IsPullback.of_right houter hab.symm hY.flip
  have hψ : (show MorphismProperty Scheme.{u} from
      @Surjective ⊓ @Flat ⊓ @QuasiCompact) ψ := by
    refine ⟨⟨inferInstance, ?_⟩, inferInstance⟩
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have hpY : (show MorphismProperty Scheme.{u} from
      @Surjective ⊓ @Flat ⊓ @QuasiCompact) pY :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) hY.flip hψ.1.1,
      MorphismProperty.of_isPullback (P := @Flat) hY.flip hψ.1.2⟩,
      MorphismProperty.of_isPullback (P := @QuasiCompact) hY.flip hψ.2⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := (show MorphismProperty Scheme.{u} from
      @Surjective ⊓ @Flat ⊓ @QuasiCompact)) hsquare hpY inferInstance

/-- An isomorphism between constant extensions of schemes descends to an actual
finite intermediate field, preserving the base and coefficient structure maps. -/
theorem exists_finiteIntermediateField_schemePairIso
    [Algebra.IsAlgebraic k L]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (A B : Scheme.{u}) (p : A ⟶ X) (q : B ⟶ X)
    [CompactSpace A] [QuasiSeparatedSpace A] [LocallyOfFinitePresentation q]
    (e : pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (p ≫ f) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (q ≫ f))
    (heX : e.hom ≫ pullback.snd _ (q ≫ f) ≫ q =
      pullback.snd _ (p ≫ f) ≫ p)
    (heL : e.hom ≫ pullback.fst _ (q ≫ f) = pullback.fst _ (p ≫ f)) :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ e₀ : pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (p ≫ f) ≅
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (q ≫ f),
        e₀.hom ≫ pullback.fst _ (q ≫ f) = pullback.fst _ (p ≫ f) ∧
        e₀.hom ≫ pullback.snd _ (q ≫ f) ≫ q =
          pullback.snd _ (p ≫ f) ≫ p ∧
        (constantFieldInverseLimitCone k L A (p ≫ f)).π.app (op s) ≫ e₀.hom =
          e.hom ≫ (constantFieldInverseLimitCone k L B (q ≫ f)).π.app (op s) := by
  obtain ⟨s, hfin, g, hgL, hgX, hrec⟩ :=
    exists_finiteIntermediateField_schemePairHom k L X f A B p q e.hom heX heL
  have : IsIso g :=
    isIso_of_constantFieldStageHom k L A B (p ≫ f) (q ≫ f) s e.hom g heL hgL hrec
  exact ⟨s, hfin, asIso g, hgL, hgX, hrec⟩

/-- A finite family of morphisms of constant-field extensions descends to one
actual finite coefficient field, preserving the two structure maps and recovery. -/
theorem exists_finiteIntermediateField_schemePairHom_family
    [Algebra.IsAlgebraic k L] {ι : Type v} [Finite ι]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    (A B : ι → Scheme.{u}) (p : ∀ i : ι, A i ⟶ X) (q : ∀ i : ι, B i ⟶ X)
    [∀ i : ι, CompactSpace (A i)] [∀ i : ι, QuasiSeparatedSpace (A i)]
    [∀ i : ι, LocallyOfFinitePresentation (q i)]
    (a : ∀ i : ι, pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (p i ≫ f) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) (q i ≫ f))
    (haX : ∀ i : ι, a i ≫ pullback.snd _ (q i ≫ f) ≫ q i =
      pullback.snd _ (p i ≫ f) ≫ p i)
    (haL : ∀ i : ι, a i ≫ pullback.fst _ (q i ≫ f) = pullback.fst _ (p i ≫ f)) :
    ∃ s : Finset L, FiniteDimensional k (IntermediateField.adjoin k (s : Set L)) ∧
      ∃ g : ∀ i : ι, pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (p i ≫ f) ⟶
        pullback (Spec.map (CommRingCat.ofHom
          (algebraMap k (IntermediateField.adjoin k (s : Set L))))) (q i ≫ f),
        ∀ i : ι, g i ≫ pullback.fst _ (q i ≫ f) = pullback.fst _ (p i ≫ f) ∧
          g i ≫ pullback.snd _ (q i ≫ f) ≫ q i =
            pullback.snd _ (p i ≫ f) ≫ p i ∧
          (constantFieldInverseLimitCone k L (A i) (p i ≫ f)).π.app (op s) ≫ g i =
            a i ≫ (constantFieldInverseLimitCone k L (B i) (q i ≫ f)).π.app (op s) := by
  classical
  let := Fintype.ofFinite ι
  choose s hfin g hgL hgX hrecovery using fun i : ι ↦
    exists_finiteIntermediateField_schemePairHom k L X f (A i) (B i) (p i) (q i)
      (a i) (haX i) (haL i)
  let T : Finset L := Finset.univ.biUnion s
  have hiT (i : ι) : s i ⊆ T := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φs (s : Finset L) := Spec.map (CommRingCat.ofHom
    (algebraMap k (IntermediateField.adjoin k (s : Set L))))
  let r (i : ι) : pullback (φs T) (p i ≫ f) ⟶ pullback (φs (s i)) (p i ≫ f) :=
    (constantFieldInverseLimitDiagram k L (A i) (p i ≫ f)).map (homOfLE (hiT i)).op
  have hr (i : ι) : r i ≫ pullback.snd (φs (s i)) (p i ≫ f) =
      pullback.snd (φs T) (p i ≫ f) :=
    Over.w ((constantFieldInverseLimitOverDiagram k L (A i) (p i ≫ f)).map
      (homOfLE (hiT i)).op)
  let b (i : ι) : pullback (φs T) (p i ≫ f) ⟶ B i :=
    r i ≫ g i ≫ pullback.snd (φs (s i)) (q i ≫ f)
  have hbX (i : ι) : b i ≫ q i = pullback.snd (φs T) (p i ≫ f) ≫ p i := by
    dsimp only [b]
    rw [Category.assoc, Category.assoc, hgX i, ← Category.assoc, hr]
  let G (i : ι) : pullback (φs T) (p i ≫ f) ⟶ pullback (φs T) (q i ≫ f) :=
    pullback.lift (pullback.fst (φs T) (p i ≫ f)) (b i) (by
      rw [← Category.assoc, hbX i, Category.assoc]
      exact pullback.condition)
  refine ⟨T, ?_, G, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral)
  intro i
  refine ⟨pullback.lift_fst _ _ _, ?_, ?_⟩
  · rw [← Category.assoc, pullback.lift_snd]
    exact hbX i
  let cAS : pullback φ (p i ≫ f) ⟶ pullback (φs (s i)) (p i ≫ f) :=
    (constantFieldInverseLimitCone k L (A i) (p i ≫ f)).π.app (op (s i))
  let cBS : pullback φ (q i ≫ f) ⟶ pullback (φs (s i)) (q i ≫ f) :=
    (constantFieldInverseLimitCone k L (B i) (q i ≫ f)).π.app (op (s i))
  let cAT : pullback φ (p i ≫ f) ⟶ pullback (φs T) (p i ≫ f) :=
    (constantFieldInverseLimitCone k L (A i) (p i ≫ f)).π.app (op T)
  let cBT : pullback φ (q i ≫ f) ⟶ pullback (φs T) (q i ≫ f) :=
    (constantFieldInverseLimitCone k L (B i) (q i ≫ f)).π.app (op T)
  have hrec : cAS ≫ g i = a i ≫ cBS := hrecovery i
  have hnat : cAT ≫ r i = cAS :=
    (constantFieldInverseLimitCone k L (A i) (p i ≫ f)).w (homOfLE (hiT i)).op
  have hcATfst : cAT ≫ pullback.fst (φs T) (p i ≫ f) =
      pullback.fst φ (p i ≫ f) ≫ Spec.map (CommRingCat.ofHom
        (IntermediateField.adjoin k (T : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L (A i) (p i ≫ f) T
  have hcBTfst : cBT ≫ pullback.fst (φs T) (q i ≫ f) =
      pullback.fst φ (q i ≫ f) ≫ Spec.map (CommRingCat.ofHom
        (IntermediateField.adjoin k (T : Set L)).val.toRingHom) :=
    constantFieldInverseLimitCone_π_app_fst k L (B i) (q i ≫ f) T
  have hcBSsnd : cBS ≫ pullback.snd (φs (s i)) (q i ≫ f) =
      pullback.snd φ (q i ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L (B i) (q i ≫ f)).π.app (op (s i)))
  have hcBTsnd : cBT ≫ pullback.snd (φs T) (q i ≫ f) =
      pullback.snd φ (q i ≫ f) :=
    Over.w ((constantFieldInverseLimitOverCone k L (B i) (q i ≫ f)).π.app (op T))
  change cAT ≫ G i = a i ≫ cBT
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, hcBTfst,
      ← Category.assoc, haL i]
    exact hcATfst
  · rw [Category.assoc, pullback.lift_snd]
    change cAT ≫ (r i ≫ g i ≫ pullback.snd (φs (s i)) (q i ≫ f)) = _
    rw [← Category.assoc, ← Category.assoc, hnat, hrec,
      Category.assoc, hcBSsnd, Category.assoc, hcBTsnd]

end EtaleFundamentalGroups
