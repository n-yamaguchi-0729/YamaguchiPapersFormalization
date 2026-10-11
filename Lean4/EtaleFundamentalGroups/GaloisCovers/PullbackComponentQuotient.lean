/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponent
import EtaleFundamentalGroups.Inertia.DivisorialStrictHenselian
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Quotients attached to pointed pullback components

A pointed connected Galois component of the pullback of a pointed Galois
cover has the same stabilizer kernel as the restricted original quotient.
The component quotient therefore induces an injective homomorphism from the
component deck group to the original deck group.  In particular, mapping a
subgroup along this homomorphism preserves its cardinality and all numerical
coprimality statements.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- The pointed quotient of a Galois pullback component and the restricted
pointed quotient of the original cover have the same kernel. -/
theorem galoisPullbackComponent_quotient_ker_eq
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i) :
    letI : IsGalois Z := hZ
    (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
      xi Z hZ z).ker =
      (EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
        f xi A hA x).ker := by
  let : IsGalois Z := hZ
  let : Mono i := hi
  rw [EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_ker,
    EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism_ker]
  let y : (fiber xi).obj ((pullback f).obj A) :=
    transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x
  have hi_injective : Function.Injective ((fiber xi).map i) := by
    let : Mono ((fiber xi).map i) := Functor.map_mono (fiber xi) i
    exact ConcreteCategory.injective_of_mono_of_preservesPullback
      ((fiber xi).map i)
  change MulAction.stabilizer π₁ᵉᵗ(xi) z =
    MulAction.stabilizer π₁ᵉᵗ(xi) y
  ext a
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro ha
    calc
      a • y = a • (fiber xi).map i z :=
        congrArg (fun q ↦ a • q) hiz.symm
      _ = (fiber xi).map i (a • z) :=
        mulAction_naturality (fiber xi) a i z
      _ = (fiber xi).map i z := congrArg ((fiber xi).map i) ha
      _ = y := hiz
  · intro ha
    apply hi_injective
    calc
      (fiber xi).map i (a • z) = a • (fiber xi).map i z :=
        (mulAction_naturality (fiber xi) a i z).symm
      _ = a • y := congrArg (fun q ↦ a • q) hiz
      _ = y := ha
      _ = (fiber xi).map i z := hiz.symm

/-- The canonical deck-group homomorphism induced by a pointed Galois
component of a pullback.  It is characterized by composing with the
surjective component quotient to give the restricted original quotient. -/
noncomputable def galoisPullbackComponentQuotientMonoidHom
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i) :
    (Aut Z)ᵐᵒᵖ →* (Aut A)ᵐᵒᵖ := by
  letI : IsGalois Z := hZ
  let qZ := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi Z hZ z
  let qA :=
    EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
      f xi A hA x
  exact qZ.liftOfSurjective
    (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi Z hZ z)
    ⟨qA, (galoisPullbackComponent_quotient_ker_eq
      f xi A hA x Z i z hiz hZ hi).le⟩

/-- The component-to-original deck homomorphism composes with the component
quotient to give the restricted original quotient. -/
theorem galoisPullbackComponentQuotientMonoidHom_comp
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i) :
    letI : IsGalois Z := hZ
    (galoisPullbackComponentQuotientMonoidHom
      f xi A hA x Z i z hiz hZ hi).comp
        (EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi Z hZ z) =
      EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
        f xi A hA x := by
  let : IsGalois Z := hZ
  let qZ := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi Z hZ z
  let qA :=
    EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
      f xi A hA x
  let hqZ :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi Z hZ z
  let hker : qZ.ker ≤ qA.ker :=
    (galoisPullbackComponent_quotient_ker_eq
      f xi A hA x Z i z hiz hZ hi).le
  apply MonoidHom.ext
  intro a
  exact MonoidHom.liftOfRightInverse_comp_apply
    (f := qZ) (f_inv := Function.surjInv hqZ)
    (Function.rightInverse_surjInv hqZ) ⟨qA, hker⟩ a

/-- The canonical homomorphism from component deck transformations to
original deck transformations is injective. -/
theorem galoisPullbackComponentQuotientMonoidHom_injective
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i) :
    Function.Injective
      (galoisPullbackComponentQuotientMonoidHom
        f xi A hA x Z i z hiz hZ hi) := by
  let : IsGalois Z := hZ
  let qZ := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi Z hZ z
  let qA :=
    EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
      f xi A hA x
  let φ := galoisPullbackComponentQuotientMonoidHom
    f xi A hA x Z i z hiz hZ hi
  have hqZ : Function.Surjective qZ :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi Z hZ z
  have hker : qZ.ker = qA.ker :=
    galoisPullbackComponent_quotient_ker_eq
      f xi A hA x Z i z hiz hZ hi
  have hcomp : φ.comp qZ = qA :=
    galoisPullbackComponentQuotientMonoidHom_comp
      f xi A hA x Z i z hiz hZ hi
  intro a b hab
  obtain ⟨g, rfl⟩ := hqZ a
  obtain ⟨h, rfl⟩ := hqZ b
  apply qZ.eq_iff.mpr
  rw [hker]
  apply qA.eq_iff.mp
  calc
    qA g = φ (qZ g) := (MonoidHom.ext_iff.mp hcomp g).symm
    _ = φ (qZ h) := hab
    _ = qA h := MonoidHom.ext_iff.mp hcomp h

/-- The image of the component deck group is exactly the local-monodromy
range of the original cover. -/
theorem galoisPullbackComponentQuotientMonoidHom_range
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i) :
    (galoisPullbackComponentQuotientMonoidHom
      f xi A hA x Z i z hiz hZ hi).range =
      (EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
        f xi A hA x).range := by
  let : IsGalois Z := hZ
  let qZ := EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
    xi Z hZ z
  let qA :=
    EtaleFundamentalGroups.Inertia.finiteEtaleGaloisCoverQuotientOfMorphism
      f xi A hA x
  let φ := galoisPullbackComponentQuotientMonoidHom
    f xi A hA x Z i z hiz hZ hi
  have hqZ : Function.Surjective qZ :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom_surjective
      xi Z hZ z
  have hcomp : φ.comp qZ = qA :=
    galoisPullbackComponentQuotientMonoidHom_comp
      f xi A hA x Z i z hiz hZ hi
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨g, hg⟩ := hqZ b
    refine ⟨g, ?_⟩
    calc
      qA g = φ (qZ g) := (MonoidHom.ext_iff.mp hcomp g).symm
      _ = φ b := congrArg φ hg
  · rintro ⟨g, rfl⟩
    exact ⟨qZ g, MonoidHom.ext_iff.mp hcomp g⟩

/-- Mapping a subgroup of the component deck group into the original deck
group preserves its cardinality. -/
theorem galoisPullbackComponentQuotientMonoidHom_map_natCard
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i)
    (H : Subgroup (Aut Z)ᵐᵒᵖ) :
    Nat.card (H.map (galoisPullbackComponentQuotientMonoidHom
      f xi A hA x Z i z hiz hZ hi)) = Nat.card H := by
  exact Subgroup.card_map_of_injective
    (galoisPullbackComponentQuotientMonoidHom_injective
      f xi A hA x Z i z hiz hZ hi)

/-- Coprimality of a component deck subgroup is unchanged after mapping it
to the original deck group. -/
theorem galoisPullbackComponentQuotientMonoidHom_map_coprime_iff
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (hA : IsGalois A)
    (x : (fiber (xi ≫ f)).obj A)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj A)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x)
    (hZ : IsGalois Z) (hi : Mono i)
    (H : Subgroup (Aut Z)ᵐᵒᵖ) (n : ℕ) :
    Nat.Coprime
        (Nat.card (H.map (galoisPullbackComponentQuotientMonoidHom
          f xi A hA x Z i z hiz hZ hi))) n ↔
      Nat.Coprime (Nat.card H) n := by
  rw [galoisPullbackComponentQuotientMonoidHom_map_natCard]

end AlgebraicGeometry.FiniteEtale

end
