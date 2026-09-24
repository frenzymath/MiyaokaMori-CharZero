import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyTransportSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationEpi
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackIdMonoidal

/-! # Unit tracking for the evaluation `α_n` and for the chart twist isomorphism

Helper module for `RelativeProjLiftEvaluationTwistFamilyTransport.lean`. Notation: `π := (relativeProj S).hom`, `W : X.affineOpens`,
`𝒜 := S.sectionsGrading W`, `e := affineIso S W : π⁻¹W ≅ Proj 𝒜`, `ι_W := (π⁻¹W).ι`, `N := twist S n`,
`G := Proj.twist 𝒜 n`, `s := evaluationLocal S n W x ∈ Γ(N, π⁻¹W)`, `t := twistSection 𝒜 (sectionsOf x) ∈ Γ(G, ⊤)`.

* `restrict_hom_app_map_tfam`: a morphism out of `M.restrict j` commutes with restriction, written with the ambient
  opens (`hom_app_presheaf_map` + Mathlib `restrict_map`).
* `pullbackId_hom_app_pullbackSectionsOn_tfam`: `(pullbackId X).hom` on `(𝟙^*a)|_U` is `a|_U`
  (`pullbackId_hom_app_unit_app_apply`).
* `evaluation_comp_app_pullbackSectionsOn`: `((pullbackComp τ π)⁻¹ ≫ τ^*(evaluation S n))` on `((τ ≫ π)^*x)|_B` is
  `(τ^*s)|_B` (`pullbackComp_inv_app_pullbackSectionsOn`, `pullback_map_app_pullbackSectionsOn_bc`,
  `evaluation_app_unit`).
* `twistAffineIso_hom_app_unit_evaluationLocal`: `(rFIP ι_W)⁻¹ ≫ (twistAffineIso S W n).hom` on `η_{ι_W}(s)` is
  `(e^*t)|_{ι_W⁻¹(π⁻¹W)}` (`evaluationLocal_eq`, `restrictFunctorIsoPullback_inv_app_pullbackSectionsOn`,
  `modIso_hom_app_inv_app`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- A morphism out of a restriction commutes with restriction, written with the ambient opens
(`hom_app_presheaf_map` + `restrict_map`). -/
theorem restrict_hom_app_map_tfam (j : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion j] {M : X.Modules}
    {P : Y.Modules} (φ : M.restrict j ⟶ P) {A' B' : Y.Opens} (h : B' ≤ A') (hB : j ''ᵁ B' ≤ j ''ᵁ A')
    (x : Γ(M, j ''ᵁ A')) :
    φ.app B' (M.presheaf.map (homOfLE hB).op x) =
      P.presheaf.map (homOfLE h).op (φ.app A' x) := by
  have := AlgebraicGeometry.Scheme.Modules.app_map (M := M.restrict j) φ h x
  rw [AlgebraicGeometry.Scheme.Modules.restrict_map] at this
  have e : j.opensFunctor.map (homOfLE h) = homOfLE hB := Subsingleton.elim _ _
  rw [e] at this
  exact this

/-- `(pullbackId X).hom` on the pulled-back section `(𝟙^*a)|_U` is `a|_U`. -/
theorem pullbackId_hom_app_pullbackSectionsOn_tfam (A : X.Modules) (V U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ V)
    (a : Γ(A, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).app A).hom.app U
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (𝟙 X) A V U h a) =
      A.presheaf.map (homOfLE h).op a := by
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_apply,
    AlgebraicGeometry.Scheme.Modules.app_map]
  exact congrArg _ (AlgebraicGeometry.Scheme.Modules.pullbackId_hom_app_unit_app_apply X A V a)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-- **`α_n` on a pulled-back section**: for `τ : T ⟶ P`, `B ≤ (τ ≫ π)⁻¹W`, `x ∈ Γ(W, S_n)`,
`((pullbackComp τ π)⁻¹ ≫ τ^*(evaluation S n))(((τ ≫ π)^*x)|_B) = (τ^*(evaluationLocal S n W x))|_B`. -/
theorem evaluation_comp_app_pullbackSectionsOn (S : X.GradedQCAlgebra) (n : ℕ) (W : X.affineOpens)
    (τ : T ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left) (B : T.Opens)
    (h₀ : B ≤ (τ ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom) ⁻¹ᵁ W.1)
    (h₁ : B ≤ τ ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)) (x : Γ(S.part n, W.1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp τ (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app
          (S.part n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback τ).map (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)).app B
        (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
          (τ ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom) (S.part n) W.1 B h₀ x) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn τ (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) B h₁
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x) := by
  change ((AlgebraicGeometry.Scheme.Modules.pullback τ).map (AlgebraicGeometry.Scheme.relativeProj.evaluation S n)).app B
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp τ (AlgebraicGeometry.Scheme.relativeProj S).hom).app
        (S.part n)).inv.app B
      (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
        (τ ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom) (S.part n) W.1 B h₀ x)) = _
  rw [AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_app_pullbackSectionsOn τ
    (AlgebraicGeometry.Scheme.relativeProj S).hom (S.part n) W.1 B h₁ h₀ x,
    AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn_bc]
  exact congrArg _ (AlgebraicGeometry.Scheme.relativeProj.evaluation_app_unit S n W x)

/-- **The chart step of `α_n`**: with `s := evaluationLocal S n W x` and `W' := ι_W⁻¹(π⁻¹W)`,
`(twistAffineIso S W n).hom ((rFIP ι_W)⁻¹ (η_{ι_W} s)) = (η_e t)|_{W'}` where `t := twistSection 𝒜 (sectionsOf x)`.
By `evaluationLocal_eq`, `s = ((twistAffineIso)⁻¹(η_e t))|_{π⁻¹W}`; `(rFIP)⁻¹` undoes the pullback of a section of
`N|_{π⁻¹W}` (`restrictFunctorIsoPullback_inv_app_pullbackSectionsOn`), and `twistAffineIso.hom ∘ .inv = id`. -/
theorem twistAffineIso_hom_app_unit_evaluationLocal (S : X.GradedQCAlgebra) (n : ℕ) (W : X.affineOpens)
    (x : Γ(S.part n, W.1)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (n : ℤ)).hom.app
        (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1))
        (((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
            ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι).app
            (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).inv.app
          (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ⁻¹ᵁ
            ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1))
          (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι
            (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))
            ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)
            (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x))) =
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom).obj
          (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ))).presheaf.map
        (homOfLE (le_top : (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι ⁻¹ᵁ
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1)) ≤
            (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom ⁻¹ᵁ ⊤)).op
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom
          (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)) ⊤
          (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading W.1) (S.sectionsOf W.1 n x).1
            (S.sectionsOf W.1 n x).2)) := by
  -- abbreviations
  set ιW := ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1).ι with hιW
  set N := AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ) with hN
  set s := AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S n W x with hs
  set W' := ιW ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) with hW'
  -- the section `y' := (twistAffineIso)⁻¹(η_e t) ∈ Γ(N, ι_W '' ⊤)`, of which `s` is the restriction
  set y' : Γ(N, ιW ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom ⁻¹ᵁ ⊤)) :=
    ((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (n : ℤ)).inv.app
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom ⁻¹ᵁ ⊤))
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)) ⊤
        (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading W.1) (S.sectionsOf W.1 n x).1
          (S.sectionsOf W.1 n x).2)) with hy'
  have hs' : s = N.presheaf.map (homOfLE (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S W)).op y' :=
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq S n W x
  -- step 1: `η_{ι_W} s = ((ι_W)^*(s|_{ι_W '' W'}))|_{W'}`
  have k₂ : W' ≤ ιW ⁻¹ᵁ (ιW ''ᵁ W') := le_of_eq (ιW.preimage_image_eq W').symm
  have hipl : ιW ''ᵁ W' ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1 :=
    ιW.image_preimage_le _
  have h1 : AlgebraicGeometry.Scheme.Modules.pullbackUnitHom ιW N
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ W.1) s =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn ιW N (ιW ''ᵁ W') W' k₂
        (N.presheaf.map (homOfLE hipl).op s) := by
    rw [← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_self ιW N _ s]
    exact AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res ιW N le_rfl k₂ hipl s
  rw [h1, AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_inv_app_pullbackSectionsOn]
  -- step 2: `s|_{ι_W '' W'} = y'|_{ι_W '' W'}` as a restriction of `y'` along `ι_W '' W' ≤ ι_W '' ⊤`
  have hB : ιW ''ᵁ W' ≤ ιW ''ᵁ ((AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom ⁻¹ᵁ ⊤) :=
    hipl.trans (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S W)
  have h2 : N.presheaf.map (homOfLE hipl).op s = N.presheaf.map (homOfLE hB).op y' := by
    rw [hs']
    exact AlgebraicGeometry.Scheme.Modules.famRes_comp' N
      (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S W) hipl y'
  rw [h2]
  -- step 3: `twistAffineIso.hom` commutes with restriction, and undoes `.inv`
  exact (AlgebraicGeometry.Scheme.Modules.restrict_hom_app_map_tfam ιW
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (n : ℤ)).hom
    (le_top : W' ≤ (AlgebraicGeometry.Scheme.relativeProj.affineIso S W).hom ⁻¹ᵁ ⊤) hB y').trans
    (congrArg _ (AlgebraicGeometry.Scheme.Modules.modIso_hom_app_inv_app
      (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S W (n : ℤ)) _ _))

end AlgebraicGeometry.Scheme.relativeProj

end
