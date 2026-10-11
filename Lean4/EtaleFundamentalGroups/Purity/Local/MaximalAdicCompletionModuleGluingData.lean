/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.MaximalAdicCompletionMixedEqualizer
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Module data for maximal-adic formal gluing

This file packages the degree-zero Cech diagram used in formal gluing.  A
datum has one completion module, one module on every principal chart, common
completion/chart overlap modules, and common chart/chart overlap modules.
Its global sections are the simultaneous equalizer of all restriction maps.

For the standard datum attached to an `R`-module `M`, the completion chart is
`Rhat tensor M`, the principal charts are the localized modules `M_f`, and
the overlap maps are the canonical localization maps.  The mixed equalizer
theorem identifies the resulting global-sections module with `M`.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- A degree-zero module gluing diagram.  Besides the completion/principal
overlaps, it records every principal/principal overlap; equality of the two
maps to these latter objects is the punctured Cech cocycle condition. -/
structure ModuleFormalGluingDatum
    (R : Type u) [CommRing R] (ι : Type v) where
  /-- The module on the completion chart. -/
  completion : ModuleCat.{w} R
  /-- The module on each principal chart. -/
  principal : ι → ModuleCat.{w} R
  /-- The common module on each completion/principal overlap. -/
  completionLocalOverlap : ι → ModuleCat.{w} R
  /-- The common module on each ordered pair of principal charts. -/
  principalOverlap : ι → ι → ModuleCat.{w} R
  /-- Restriction from the completion chart to each common overlap. -/
  completionRestriction :
    (i : ι) → completion ⟶ completionLocalOverlap i
  /-- Restriction from each principal chart to its completion overlap. -/
  localToCompletionOverlap :
    (i : ι) → principal i ⟶ completionLocalOverlap i
  /-- Restriction from the first principal chart to a pairwise overlap. -/
  localRestrictionLeft :
    (i j : ι) → principal i ⟶ principalOverlap i j
  /-- Restriction from the second principal chart to a pairwise overlap. -/
  localRestrictionRight :
    (i j : ι) → principal j ⟶ principalOverlap i j

namespace ModuleFormalGluingDatum

variable {R : Type u} [CommRing R] {ι : Type v}
variable (D : ModuleFormalGluingDatum.{u, v, w} R ι)

/-- The completion component together with all principal-chart components. -/
abbrev Source :=
  D.completion × ((i : ι) → D.principal i)

/-- The completion/principal overlap components. -/
abbrev CompletionLocalTarget :=
  (i : ι) → D.completionLocalOverlap i

/-- The degree-one Cech components for the punctured principal cover. -/
abbrev PuncturedCechTarget :=
  (i : ι) → (j : ι) → D.principalOverlap i j

/-- All overlap components in the formal-gluing diagram. -/
abbrev Target :=
  D.CompletionLocalTarget × D.PuncturedCechTarget

/-- Restrict the completion component to every completion/principal
overlap. -/
def completionLocalLeft :
    D.Source →ₗ[R] D.CompletionLocalTarget :=
  LinearMap.pi fun i ↦
    (D.completionRestriction i).hom.comp
      (LinearMap.fst R D.completion ((i : ι) → D.principal i))

/-- Restrict each principal component to its completion/principal overlap. -/
def completionLocalRight :
    D.Source →ₗ[R] D.CompletionLocalTarget :=
  LinearMap.pi fun i ↦
    (D.localToCompletionOverlap i).hom.comp <|
      (LinearMap.proj i).comp
        (LinearMap.snd R D.completion ((i : ι) → D.principal i))

/-- The first restriction of every ordered pair of principal components. -/
def puncturedCechLeft :
    ((i : ι) → D.principal i) →ₗ[R] D.PuncturedCechTarget :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (D.localRestrictionLeft i j).hom.comp (LinearMap.proj i)

/-- The second restriction of every ordered pair of principal components. -/
def puncturedCechRight :
    ((i : ι) → D.principal i) →ₗ[R] D.PuncturedCechTarget :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (D.localRestrictionRight i j).hom.comp (LinearMap.proj j)

/-- Local tuples satisfying all pairwise Cech cocycle equations. -/
abbrev PuncturedCechSections :=
  LinearMap.eqLocus D.puncturedCechLeft D.puncturedCechRight

/-- The first map of the simultaneous formal-gluing equalizer. -/
def left : D.Source →ₗ[R] D.Target :=
  D.completionLocalLeft.prod <|
    D.puncturedCechLeft.comp
      (LinearMap.snd R D.completion ((i : ι) → D.principal i))

/-- The second map of the simultaneous formal-gluing equalizer. -/
def right : D.Source →ₗ[R] D.Target :=
  D.completionLocalRight.prod <|
    D.puncturedCechRight.comp
      (LinearMap.snd R D.completion ((i : ι) → D.principal i))

/-- The `H^0` module of a formal-gluing datum. -/
abbrev Sections :=
  LinearMap.eqLocus D.left D.right

/-- Membership in `H^0` is exactly completion/local compatibility together
with the punctured Cech cocycle condition. -/
theorem mem_sections_iff (x : D.Source) :
    x ∈ D.Sections ↔
      D.completionLocalLeft x = D.completionLocalRight x ∧
        D.puncturedCechLeft x.2 = D.puncturedCechRight x.2 := by
  change D.left x = D.right x ↔ _
  constructor
  · intro hx
    exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  · rintro ⟨hcompletion, hcech⟩
    exact Prod.ext hcompletion hcech

/-- Forget the completion component of a global section and retain its
punctured Cech section. -/
def sectionsToPuncturedCech :
    D.Sections →ₗ[R] D.PuncturedCechSections :=
  LinearMap.codRestrict D.PuncturedCechSections
    ((LinearMap.snd R D.completion ((i : ι) → D.principal i)).comp
      D.Sections.subtype) <| by
        intro x
        have hx := congrArg Prod.snd x.2
        exact hx

/-- The canonical map from global sections to the completion component. -/
def completionProjection : D.Sections →ₗ[R] D.completion :=
  (LinearMap.fst R D.completion ((i : ι) → D.principal i)).comp
    D.Sections.subtype

/-- The canonical map from global sections to a principal component. -/
def localProjection (i : ι) : D.Sections →ₗ[R] D.principal i :=
  (LinearMap.proj i).comp <|
    (LinearMap.snd R D.completion ((i : ι) → D.principal i)).comp
      D.Sections.subtype

@[simp]
theorem completionProjection_apply (x : D.Sections) :
    D.completionProjection x = x.1.1 :=
  rfl

@[simp]
theorem localProjection_apply (x : D.Sections) (i : ι) :
    D.localProjection i x = x.1.2 i :=
  rfl

end ModuleFormalGluingDatum

section MaximalAdic

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type w) [AddCommGroup M] [Module R M]

private abbrev GluingRhat :=
  AdicCompletion (maximalIdeal R) R

private abbrev GluingGeneratorIndex :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGeneratorIndex R

private abbrev gluingGenerator (i : GluingGeneratorIndex R) : R :=
  AlgebraicGeometry.Scheme.puncturedSpectrumGenerator R i

private abbrev GluingPowers (i : GluingGeneratorIndex R) : Submonoid R :=
  Submonoid.powers (gluingGenerator R i)

/-- The standard formal-gluing datum attached to an `R`-module. -/
def maximalAdicCompletionStandardModuleGluingDatum :
    ModuleFormalGluingDatum R (GluingGeneratorIndex R) where
  completion := ModuleCat.of R (GluingRhat R ⊗[R] M)
  principal i := ModuleCat.of R (LocalizedModule (GluingPowers R i) M)
  completionLocalOverlap i :=
    ModuleCat.of R
      (LocalizedModule (GluingPowers R i) (GluingRhat R ⊗[R] M))
  principalOverlap i j :=
    ModuleCat.of R
      (LocalizedModule (GluingPowers R j)
        (LocalizedModule (GluingPowers R i) M))
  completionRestriction i := ModuleCat.ofHom <|
    LocalizedModule.mkLinearMap
      (GluingPowers R i) (GluingRhat R ⊗[R] M)
  localToCompletionOverlap i := ModuleCat.ofHom <|
    IsLocalizedModule.map (GluingPowers R i)
      (LocalizedModule.mkLinearMap (GluingPowers R i) M)
      (LocalizedModule.mkLinearMap
        (GluingPowers R i) (GluingRhat R ⊗[R] M))
      (TensorProduct.mk R (GluingRhat R) M 1)
  localRestrictionLeft i j := ModuleCat.ofHom <|
    LocalizedModule.mkLinearMap (GluingPowers R j)
      (LocalizedModule (GluingPowers R i) M)
  localRestrictionRight i j := ModuleCat.ofHom <|
    IsLocalizedModule.map (GluingPowers R j)
      (LocalizedModule.mkLinearMap (GluingPowers R j) M)
      (LocalizedModule.mkLinearMap (GluingPowers R j)
        (LocalizedModule (GluingPowers R i) M))
      (LocalizedModule.mkLinearMap (GluingPowers R i) M)

private abbrev StandardGluingDatum :=
  maximalAdicCompletionStandardModuleGluingDatum R M

/-- The canonical completion/localization tuple is a section of the
standard formal-gluing datum. -/
def maximalAdicCompletionStandardModuleGluingMap :
    M →ₗ[R] (StandardGluingDatum R M).Sections :=
  LinearMap.codRestrict (StandardGluingDatum R M).Sections
    ((TensorProduct.mk R (GluingRhat R) M 1).prod <|
      LinearMap.pi fun i ↦
        LocalizedModule.mkLinearMap (GluingPowers R i) M) <| by
          intro m
          apply Prod.ext
          · exact (maximalAdicCompletionMixedEqualizerMap R M m).2
          · funext i j
            change LocalizedModule.mk (LocalizedModule.mk m 1) 1 =
              IsLocalizedModule.map (GluingPowers R j)
                (LocalizedModule.mkLinearMap (GluingPowers R j) M)
                (LocalizedModule.mkLinearMap (GluingPowers R j)
                  (LocalizedModule (GluingPowers R i) M))
                (LocalizedModule.mkLinearMap (GluingPowers R i) M)
                (LocalizedModule.mk m 1)
            symm
            exact IsLocalizedModule.map_LocalizedModules
              (GluingPowers R j)
              (LocalizedModule.mkLinearMap (GluingPowers R i) M) m 1

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionStandardModuleGluingMap_completion (m : M) :
    (maximalAdicCompletionStandardModuleGluingMap R M m).1.1 =
      1 ⊗ₜ[R] m :=
  rfl

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionStandardModuleGluingMap_localization
    (m : M) (i : GluingGeneratorIndex R) :
    (maximalAdicCompletionStandardModuleGluingMap R M m).1.2 i =
      LocalizedModule.mk m 1 :=
  rfl

/-- The canonical punctured Cech section associated to an `R`-module
element.  This is the degree-zero source used before the completion
component is imposed. -/
def maximalAdicCompletionStandardPuncturedCechMap :
    M →ₗ[R] (StandardGluingDatum R M).PuncturedCechSections :=
  (StandardGluingDatum R M).sectionsToPuncturedCech.comp
    (maximalAdicCompletionStandardModuleGluingMap R M)

omit [IsNoetherianRing R] in
@[simp]
theorem maximalAdicCompletionStandardPuncturedCechMap_apply
    (m : M) :
    (maximalAdicCompletionStandardPuncturedCechMap R M m).1 =
      fun i ↦ LocalizedModule.mkLinearMap (GluingPowers R i) M m :=
  rfl

/-- The kernel of restriction to the punctured Cech diagram is
maximal-ideal-power torsion. -/
theorem exists_pow_annihilates_of_standardPuncturedCechMap_eq_zero
    (m : M)
    (hm : maximalAdicCompletionStandardPuncturedCechMap R M m = 0) :
    ∃ n : ℕ, ∀ r : ((maximalIdeal R) ^ n : Ideal R), r.1 • m = 0 := by
  have hloc : ∀ i : GluingGeneratorIndex R,
      LocalizedModule.mkLinearMap (GluingPowers R i) M m = 0 := by
    intro i
    have hm' := congrArg (fun z ↦ z.1 i) hm
    change LocalizedModule.mkLinearMap (GluingPowers R i) M m = 0 at hm'
    exact hm'
  have hspan :
      Ideal.span (Set.range (gluingGenerator R)) = maximalIdeal R := by
    have hrange :
        Set.range (gluingGenerator R) = (maximalIdeal R).generators := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact i.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hrange]
    exact (maximalIdeal R).span_generators
  exact exists_pow_annihilates_of_localizedModule_mk_eq_zero
    (maximalIdeal R).fg_of_isNoetherianRing (gluingGenerator R) hspan m hloc

/-- The `H^0` of the standard completion/principal Cech datum is the
original module.  This is the object-level source for formal-gluing
effectivity; comparison with arbitrary datum components is handled
separately. -/
noncomputable def maximalAdicCompletionStandardModuleGluingSectionsEquiv :
    M ≃ₗ[R] (StandardGluingDatum R M).Sections :=
  LinearEquiv.ofBijective
    (maximalAdicCompletionStandardModuleGluingMap R M) <| by
      constructor
      · intro m n hmn
        apply (maximalAdicCompletionMixedEqualizerEquiv R M).injective
        apply Subtype.ext
        exact congrArg (fun z ↦ z.1) hmn
      · intro x
        let q : LinearMap.eqLocus
            (maximalAdicCompletionMixedLeft R M)
            (maximalAdicCompletionMixedRight R M) :=
          ⟨x.1, congrArg Prod.fst x.2⟩
        let m : M := (maximalAdicCompletionMixedEqualizerEquiv R M).symm q
        refine ⟨m, Subtype.ext ?_⟩
        have hq :
            ((maximalAdicCompletionMixedEqualizerEquiv R M m).1 :
                MaximalAdicCompletionMixedSource R M) = q.1 := by
          simpa only [m] using congrArg Subtype.val
            ((maximalAdicCompletionMixedEqualizerEquiv R M).apply_symm_apply q)
        exact hq

@[simp]
theorem maximalAdicCompletionStandardModuleGluingSectionsEquiv_apply
    (m : M) :
    maximalAdicCompletionStandardModuleGluingSectionsEquiv R M m =
      maximalAdicCompletionStandardModuleGluingMap R M m :=
  rfl

end MaximalAdic

end EtaleFundamentalGroups

end
