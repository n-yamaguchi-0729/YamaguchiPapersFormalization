/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PolarisationRosati.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.PolarisedAbelianScheme
import AlgebraicCurves.Foundations.Algebra.SheafOfModules_MonoidalV2

/-!
# Polarisation Rosati
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L :
  RelativeGroupLaw S f)

/-- The identity morphism regarded as a point of the scheme over its base. -/
def idPt : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

/-- The scheme morphism implementing inversion in the relative group law. -/
def negMor : A ⟶ A := (L.inv f (idPt f)).1

theorem negMor_over : negMor f L ≫ f = f := (L.inv f (idPt f)).2

/-- The scheme morphism implementing multiplication in the relative group law. -/
def addMor : pullback f f ⟶ A :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
    pullback.condition.symm⟩).1

theorem addMor_over : addMor f L ≫ f = pullback.fst f f ≫ f :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
    pullback.condition.symm⟩).2

/-- The module sheaves become isomorphic locally on the base spectrum. -/
def LocIsoOnBase {S' : Type u} [CommRing S'] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S')) (M
  M' : X.Modules) : Prop :=
  ∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj M ≅ (Scheme.Modules.pullback (g ⁻¹ᵁ
      U).ι).obj M')

/-- The module sheaf is locally isomorphic on the base to its pullback under inversion. -/
def IsSymmetric (𝓛 : A.Modules) : Prop :=
  LocIsoOnBase f ((Scheme.Modules.pullback (negMor f L)).obj 𝓛) 𝓛

/-- The pullback under addition tensored with the duals pulled back from both factors. -/
def mumfordBundle (𝓛 : A.Modules) : (pullback f f).Modules :=
  (Scheme.Modules.pullback (addMor f L)).obj 𝓛 ⊗
    ((Scheme.Modules.pullback (pullback.fst f f)).obj (Scheme.Modules.dual 𝓛) ⊗
      (Scheme.Modules.pullback (pullback.snd f f)).obj (Scheme.Modules.dual 𝓛))

/-- The morphism into the square of the scheme defined by a point in the second factor. -/
def sliceAt {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of S)} (x : SchemeHomOver t f) :
    pullback f t ⟶ pullback f f :=
  pullback.lift (pullback.fst f t) (pullback.snd f t ≫ x.1)
    (by rw [Category.assoc, x.2]; exact pullback.condition)

/-- Local triviality of the sliced Mumford bundle forces the point to be the identity. -/
def KernelTrivial (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f
          t).Modules)) →
      x = L.one t

/-- Local triviality of the sliced Mumford bundle is equivalent to the point being two-torsion. -/
def KernelIsTwoTorsion (𝓛 : A.Modules) : Prop :=
  ∀ (R : Type u) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f),
    LocIsoOnBase (pullback.snd f t)
        ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) (𝟙_ ((pullback f
          t).Modules)) ↔
      L.mul t x x = L.one t

/-- The action and its adjoint give locally isomorphic pullbacks of the Mumford bundle. -/
def RosatiCompatible (𝓛 : A.Modules) {I : Type v} (ι : I → (A ⟶ A)) (hι : ∀ b, ι b ≫ f = f) (star :
  I → I) : Prop :=
  ∀ b : I,
    LocIsoOnBase (pullback.fst f f ≫ f)
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ ι b)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))
      ((Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f ≫ ι (star b)) (pullback.snd f f)
            (by rw [Category.assoc, hι]; exact pullback.condition))).obj (mumfordBundle f L 𝓛))

end AlgebraicGeometry.Polarisation

end
