/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.Injectivity
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Injectivity from essential surjectivity of finite-etale pullback

If pullback of finite-etale covers along a scheme morphism is essentially
surjective, then the induced homomorphism on automorphism groups of geometric
fiber functors is injective. The categorical result requires no fullness
assumption.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Essential surjectivity of finite-etale pullback implies injectivity of
the induced homomorphism on etale fundamental groups. -/
theorem fundamentalGroupHom_injective_of_pullback_essSurj
    (f : X ⟶ Y) [(pullback f).EssSurj]
    (ξ : Spec (.of Ω) ⟶ X) :
    Function.Injective (fundamentalGroupHom f ξ) :=
  autHomOfCompIso_injective_of_essSurj
    (pullback f) (pullbackFiberIso f ξ)

end AlgebraicGeometry.FiniteEtale
