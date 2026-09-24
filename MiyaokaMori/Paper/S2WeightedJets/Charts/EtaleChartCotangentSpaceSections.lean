import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01us
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.QcPullbackAffineSections

/-! # The cotangent space of the étale chart and the sections of `s^*Ω`

The étale chart as an algebraic extension, and the comparison of its cotangent space with the
sections of the pulled-back relative differentials.

Setting (§2.2 of the paper): `p : Z ⟶ C` with a section `s`,
`U ⊆ C` open, `W := p ⁻¹ᵁ U`, `A := Γ(U, ⊤)`, `B := Γ(W, ⊤)`, `ι := (p ∣_ U).appTop : A → B`,
`σ := (s|_U).appTop : B → A` with `σ ∘ ι = id`. Then `B` is an extension of `A` over `A`
(`etaleChartExtension`, an `Algebra.Extension A A`) whose kernel is `I = ker σ` and whose cotangent
space is `A ⊗_B Ω_{B/A}`. The theorem `etaleChart_cotangentSpace_equiv_sections` identifies this
cotangent space with `Γ(U, (s^*Ω_{Z/C})|_U)` (Stacks 01US + 01UT + 01I9).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- For a section `s` of `p` (`s ≫ p = 𝟙`), every open `U` satisfies `U ≤ s ⁻¹ᵁ p ⁻¹ᵁ U`
(indeed `s ⁻¹ᵁ p ⁻¹ᵁ U = (s ≫ p) ⁻¹ᵁ U = U`). Used to form the restriction
`s.resLE (p ⁻¹ᵁ U) U : U ⟶ p ⁻¹ᵁ U` of the section to `U`. -/
theorem etaleChart_section_le_preimage {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C) (s : C ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens) : U ≤ s ⁻¹ᵁ p ⁻¹ᵁ U := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hs, AlgebraicGeometry.Scheme.Hom.id_preimage]

/-- The restricted section `s|_U : U ⟶ p ⁻¹ᵁ U` is a section of `p ∣_ U : p ⁻¹ᵁ U ⟶ U`. -/
theorem etaleChart_resLE_comp_morphismRestrict {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C)
    (s : C ⟶ Z) (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens) :
    s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U) ≫ (p ∣_ U) =
      CategoryTheory.CategoryStruct.id U.toScheme := by
  rw [← AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE, ← cancel_mono U.ι,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_ι, hs, Category.comp_id, Category.id_comp]

/-- On global sections: `σ (ι x) = x` for `ι := (p ∣_ U)^♯`, `σ := (s|_U)^♯`. -/
theorem etaleChart_section_appTop_apply {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C)
    (s : C ⟶ Z) (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens)
    (x : Γ(U.toScheme, ⊤)) :
    (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)).appTop.hom
      ((p ∣_ U).appTop.hom x) = x := by
  have h := congrArg (fun f : U.toScheme ⟶ U.toScheme => f.appTop.hom x)
    (etaleChart_resLE_comp_morphismRestrict p s hs U)
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.id_appTop,
    CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at h
  exact h

/-- **The étale chart as an extension of `A := Γ(U, ⊤)` over itself**: `B := Γ(p ⁻¹ᵁ U, ⊤)` with
structure maps `ι := (p ∣_ U)^♯ : A → B` and `σ := (s|_U)^♯ : B → A`, `σ ∘ ι = id`.
Its kernel `P.ker` is `RingHom.ker σ` (definitionally), its cotangent `P.Cotangent` is `I/I²`
and its cotangent space `P.CotangentSpace` is `A ⊗_B Ω_{B/A}`. -/
noncomputable def etaleChartExtension {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C)
    (s : C ⟶ Z) (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens) :
    Algebra.Extension.{u} Γ(U.toScheme, ⊤) Γ(U.toScheme, ⊤) where
  Ring := Γ((p ⁻¹ᵁ U).toScheme, ⊤)
  commRing := inferInstance
  algebra₁ := (p ∣_ U).appTop.hom.toAlgebra
  algebra₂ := (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)).appTop.hom.toAlgebra
  isScalarTower :=
    letI := (p ∣_ U).appTop.hom.toAlgebra
    letI := (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)).appTop.hom.toAlgebra
    IsScalarTower.of_algebraMap_eq fun x =>
      (etaleChart_section_appTop_apply p s hs U x).symm
  σ := (p ∣_ U).appTop.hom
  algebraMap_σ x := etaleChart_section_appTop_apply p s hs U x

theorem etaleChartExtension_ker {C Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C)
    (s : C ⟶ Z) (hs : s ≫ p = CategoryTheory.CategoryStruct.id C) (U : C.Opens) :
    (etaleChartExtension p s hs U).ker =
      RingHom.ker (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)).appTop.hom := rfl

/-- An isomorphism of `𝒪ₓ`-modules induces a `Γ(X, U)`-linear isomorphism of sections over
every open `U` (the two components of the iso act on sections by `Hom.app`, which is
`Γ(X, U)`-linear by `Hom.app_smul`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.isoSectionsLinearEquiv
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  map_add' x y := (e.hom.app U).hom.map_add x y
  map_smul' r x := AlgebraicGeometry.Scheme.Modules.Hom.app_smul e.hom r x
  left_inv x := ConcreteCategory.congr_hom
    (congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ U) e.hom_inv_id) x
  right_inv x := ConcreteCategory.congr_hom
    (congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ U) e.inv_hom_id) x

/-- **Cotangent space of the chart = sections of `s^*Ω_{Z/C}` over `U`** (Stacks 01US, 01UT, 01I9).

Setting: `p : Z ⟶ C` affine with a section `s`, `U ⊆ C` an affine open, `W := p ⁻¹ᵁ U` (affine,
`IsAffineOpen.preimage` / `IsAffineHom`), `A := Γ(U, ⊤)`, `B := Γ(W, ⊤)`, `ι := (p ∣_ U)^♯`,
`σ := (s|_U)^♯`, `P := etaleChartExtension p s hs U`, so `P.CotangentSpace = A ⊗_B Ω_{B/A}`.
Conclusion: an `A`-linear isomorphism `A ⊗_B Ω_{B/A} ≃ Γ(U, (s^*Ω_{Z/C})|_U)`.

Proof.
1. (Stacks 01US, `AlgebraicGeometry.Omega_restrict_open`)
   `(Ω_{Z/C})|_W ≅ Ω_{W/U} := Omega (p ∣_ U)` (`p ∣_ U = p.resLE U W le_rfl`,
   `Scheme.Hom.resLE_eq_morphismRestrict`).
2. (Stacks 01UT, `AlgebraicGeometry.Omega_appIso`)
   for the affine opens `U ⊆ C`, `W ⊆ Z` with `W ≤ p ⁻¹ᵁ U`: `Γ(Z, W, Ω_{Z/C}) ≃ₗ[Γ(Z, W)]
   Ω[Γ(Z, W) ⁄ Γ(C, U)]`, the algebra structure being `p.appLE U W le_rfl`. Under
   `Scheme.Opens.topIso : Γ(W.toScheme, ⊤) ≅ Γ(Z, W)` (and the same for `U`) this is
   `Γ(W, Ω_{W/U}) ≃ₗ[B] Ω_{B/A}` with `B` an `A`-algebra via `ι`
   (`Scheme.Hom.appLE` versus `(p ∣_ U).appTop`: `morphismRestrict_appTop`/`appLE_eq_app`).
3. (Stacks 01I9, `AlgebraicGeometry.Scheme.Modules.pullbackSectionsIsoTensor`)
   for the morphism of affine schemes `s|_U : U ⟶ W` and the
   quasi-coherent module `Ω_{W/U}` (`Omega_isQuasicoherent`): `Γ(U, (s|_U)^*Ω_{W/U}) ≃ₗ[A]
   A ⊗_B Γ(W, Ω_{W/U})`, the `B`-algebra structure on `A` being `σ` — this is `P`'s
   `algebra₂`, so with step 2 the right side is `P.CotangentSpace = A ⊗_B Ω_{B/A}`.
4. Pullback functoriality (`Scheme.Modules.pullbackComp`, `pullbackCongr`,
   `Scheme.Hom.resLE_comp_ι : s|_U ≫ W.ι = U.ι ≫ s`): `(s|_U)^*((Ω_{Z/C})|_W) =
   (s|_U ≫ W.ι)^*Ω_{Z/C} = (U.ι ≫ s)^*Ω_{Z/C} = (s^*Ω_{Z/C})|_U`; with step 1 the left side of
   step 3 is `Γ(U, (s^*Ω_{Z/C})|_U)` (`SheafOfModules.evaluation` turns the sheaf isomorphism into
   an `A`-linear isomorphism of global sections).

As formalized: no transport along `Scheme.Opens.topIso`
is needed. Steps 1 and 4 give an isomorphism of `𝒪_U`-modules `(s^*Ω_{Z/C})|_U ≅ (s|_U)^*Ω_{W/U}`
(`pullbackComp`, `pullbackCongr`, `Omega_restrict_open`, `resLE_eq_morphismRestrict`), turned into an
`A`-linear isomorphism of global sections by `isoSectionsLinearEquiv`. Step 3 is
`pullbackSectionsIsoTensor (s|_U) Ω_{W/U}` verbatim (its algebra structure `(s|_U).appTop` is
`P.algebra₂` definitionally). Step 2 is `Omega_appIso (p ∣_ U)` on the opens `⊤ ⊆ W`, `⊤ ⊆ U`
(`isAffineOpen_top`); its algebra structure `(p ∣_ U).appLE ⊤ ⊤ _` is rewritten to `(p ∣_ U).appTop`
by `Scheme.Hom.appLE_eq_app` (`f ⁻¹ᵁ ⊤ = ⊤` is `rfl`), and `LinearEquiv.baseChange` extends it to
`A ⊗_B -`. The goal is first `show`n in the explicit form `A ⊗[B] Ω[B⁄A]` so that `P.Ring` does not
appear: Mathlib's `Algebra.Extension` instance `Algebra R₀ P.Ring` (via `compHom`) otherwise gives
instance search an `Algebra B P.Ring` different from `Algebra.id`.

Edge cases: `U = ⊥`: `A = B = 0`, both sides are zero modules. -/
theorem etaleChart_cotangentSpace_equiv_sections {C Z : AlgebraicGeometry.Scheme.{u}}
    (p : Z ⟶ C) (s : C ⟶ Z) (hs : s ≫ p = CategoryTheory.CategoryStruct.id C)
    [AlgebraicGeometry.IsAffineHom p] (U : C.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    Nonempty ((etaleChartExtension p s hs U).CotangentSpace ≃ₗ[Γ(U.toScheme, ⊤)]
      Γ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)), ⊤)) := by
  classical
  have hUa : AlgebraicGeometry.IsAffine U.toScheme := hU
  have hWa : AlgebraicGeometry.IsAffine (p ⁻¹ᵁ U).toScheme := hU.preimage p
  have := AlgebraicGeometry.Omega_isQuasicoherent (p ∣_ U)
  -- Step 1 (01US): `(Ω_{Z/C})|_W ≅ Ω_{W/U}`.
  obtain ⟨r⟩ := AlgebraicGeometry.Omega_restrict_open p (p ⁻¹ᵁ U) U le_rfl
  have hq : p.resLE U (p ⁻¹ᵁ U) le_rfl = p ∣_ U :=
    AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict p
  let r' : (AlgebraicGeometry.Scheme.Modules.pullback (p ⁻¹ᵁ U).ι).obj (AlgebraicGeometry.Omega p) ≅
      AlgebraicGeometry.Omega (p ∣_ U) :=
    r ≪≫ eqToIso (congrArg AlgebraicGeometry.Omega hq)
  -- Step 4 (pullback functoriality): `(s^*Ω)|_U ≅ (s|_U)^*(Ω|_W)`.
  have hcomm : U.ι ≫ s = s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U) ≫ (p ⁻¹ᵁ U).ι :=
    (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι s _).symm
  let sh : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U))).obj
          (AlgebraicGeometry.Omega (p ∣_ U)) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp U.ι s).app (AlgebraicGeometry.Omega p) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hcomm).app (AlgebraicGeometry.Omega p) ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)) (p ⁻¹ᵁ U).ι).symm).app
          (AlgebraicGeometry.Omega p) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback
        (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U))).mapIso r'
  let e₁ := AlgebraicGeometry.Scheme.Modules.isoSectionsLinearEquiv sh ⊤
  -- Step 3 (01I9): sections of the pullback along `s|_U : U ⟶ W` = base change.
  let _ : Algebra Γ((p ⁻¹ᵁ U).toScheme, ⊤) Γ(U.toScheme, ⊤) :=
    (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)).appTop.hom.toAlgebra
  let e₃ := AlgebraicGeometry.Scheme.Modules.pullbackSectionsIsoTensor
    (s.resLE (p ⁻¹ᵁ U) U (etaleChart_section_le_preimage p s hs U)) (AlgebraicGeometry.Omega (p ∣_ U))
  -- Step 2 (01UT): `Γ(W, Ω_{W/U}) ≃ₗ[B] Ω_{B/A}` (algebra structure `appLE`), then move to `appTop`.
  let i₁ : Algebra Γ(U.toScheme, ⊤) Γ((p ⁻¹ᵁ U).toScheme, ⊤) :=
    ((p ∣_ U).appLE ⊤ ⊤ le_rfl).hom.toAlgebra
  have e₂ : Γ(AlgebraicGeometry.Omega (p ∣_ U), ⊤) ≃ₗ[Γ((p ⁻¹ᵁ U).toScheme, ⊤)]
      Ω[Γ((p ⁻¹ᵁ U).toScheme, ⊤)⁄Γ(U.toScheme, ⊤)] :=
    AlgebraicGeometry.Omega_appIso (p ∣_ U) (AlgebraicGeometry.isAffineOpen_top U.toScheme)
      (AlgebraicGeometry.isAffineOpen_top (p ⁻¹ᵁ U).toScheme) le_rfl
  have hi : i₁ = (p ∣_ U).appTop.hom.toAlgebra :=
    congrArg RingHom.toAlgebra (congrArg CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app (p ∣_ U) (U := ⊤)))
  rw [hi] at e₂
  clear_value i₁
  subst hi
  let _ : Algebra Γ(U.toScheme, ⊤) Γ((p ⁻¹ᵁ U).toScheme, ⊤) := (p ∣_ U).appTop.hom.toAlgebra
  -- Assemble; the goal is unfolded so that `P.Ring` no longer appears (its `Algebra.Extension`
  -- instances would otherwise interfere with instance search).
  show Nonempty ((Γ(U.toScheme, ⊤) ⊗[Γ((p ⁻¹ᵁ U).toScheme, ⊤)]
      Ω[Γ((p ⁻¹ᵁ U).toScheme, ⊤)⁄Γ(U.toScheme, ⊤)]) ≃ₗ[Γ(U.toScheme, ⊤)]
    Γ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback s).obj (AlgebraicGeometry.Omega p)), ⊤))
  exact ⟨(e₁ ≪≫ₗ e₃ ≪≫ₗ LinearEquiv.baseChange _ Γ(U.toScheme, ⊤) _ _ e₂).symm⟩

end
