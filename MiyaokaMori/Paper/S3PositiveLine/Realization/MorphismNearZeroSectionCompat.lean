import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMorphismCongrIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Morphisms.StructureMorphismIsOver
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates

/-! # Morphism near zero section compat

Statement: if `Φ₀ : U → X` is the projectivization of the tuple `P` on an open `U ⊆ Tot(L)` and
`σ₀ : C̃ → U` is the zero section (i.e. `σ₀ ≫ U.ι` is the zero section of `Tot(L)`), and if
`P` restricted to the zero section is the pulled-back seed tuple `(ρ^*f_0, …, ρ^*f_N)`, then
`σ₀ ≫ Φ₀ = ρ ≫ f`.

Source: Theorem 4.2 of the paper ("On the zero section the tuple is `(ρ^*f_0,…,ρ^*f_N)` … Its
projectivization therefore defines a morphism to `X` on a Zariski neighborhood of the entire zero
section and restricts there to `f ∘ ρ`").

Proof (formalised below): compose with the closed immersion `X ↪ P^N` (a mono) and compare the two
projectivizations on `C̃`: `σ₀ ≫ Φ₀ ≫ emb` is the projectivization of `σ₀^*U.ι^*P` (pullback
formula ), `ρ ≫ f ≫ emb` is the projectivization of `ρ^*coord`
(`MMSetup.hcoord`, pullback formula again); the two tuples correspond under the canonical
isomorphism `σ₀^*U.ι^*M ≅ ρ^*A` (`pullbackComp`, `pullbackCongr`, `pullbackId`,
`eqToHom (OX_toModules 1)`), which is exactly the content of `hzero` after unfolding
`restrictToZeroSection`; conclude with .

-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/-- Two projectivizations of equal tuples agree (the non-vanishing proofs are irrelevant). -/
theorem projectivizationMorphism_congr_tuple {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    {P Q : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)} (h : P = Q)
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (hQ : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (Q ℓ) v) :
    projectivizationMorphism (k := k) M P hP = projectivizationMorphism (k := k) M Q hQ := by
  subst h; rfl

/-- Pulling back a nowhere-vanishing tuple along any morphism gives a nowhere-vanishing tuple. -/
theorem exists_not_isZeroAt_sectionPullbackAlong {V W : AlgebraicGeometry.Scheme.{u}} (g : V ⟶ W)
    (M : W.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ w : W, ∃ ℓ, ¬ IsZeroAt (P ℓ) w) (v : V) :
    ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong g (P ℓ)) v := by
  obtain ⟨ℓ, h⟩ := hP (g.base v)
  exact ⟨ℓ, not_isZeroAt_sectionPullbackAlong g M (P ℓ) v h⟩

theorem morphism_near_zero_zeroSection_compat {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ) =
      sectionPullbackAlong rho.hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
          (D.coord ℓ)))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Phi0 : U.toScheme ⟶ X.toScheme)
    (hPhi : IsTupleProjectivization
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules)
      P U Phi0)
    (sigma0 : rho.source.toScheme ⟶ U.toScheme)
    (hsigma : sigma0 ≫ U.ι = AlgebraicGeometry.Scheme.zeroSection L.toModules) :
    sigma0 ≫ Phi0 = rho.hom ≫ f := by
  obtain ⟨hU, hPhi⟩ := hPhi
  obtain ⟨hc, hcoord⟩ := D.hcoord
  -- notation
  let Nb : rho.source.toScheme.Modules :=
    (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules
  let M : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj Nb
  -- σ₀ is a k-morphism
  have hσ : sigma0.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change sigma0 ≫ (U.ι ≫ ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
      (rho.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) = _
    rw [← Category.assoc, hsigma, ← Category.assoc, AlgebraicGeometry.Scheme.zeroSection_comp,
      Category.id_comp]⟩
  have hU' := exists_not_isZeroAt_sectionPullbackAlong sigma0 _ _ hU
  have hc' := exists_not_isZeroAt_sectionPullbackAlong rho.hom _ _ hc
  rw [← cancel_mono X.embedding.emb, Category.assoc, hPhi, Category.assoc, ← hcoord,
    projectivizationMorphism_pullback sigma0 _ _ hU hU',
    projectivizationMorphism_pullback rho.hom _ _ hc hc']
  -- the canonical isomorphism σ₀^*U.ι^*M ≅ ρ^*A
  let θ : (AlgebraicGeometry.Scheme.Modules.pullback sigma0).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback rho.hom).obj (seedLineBundle X.embedding f) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp sigma0 U.ι).app M ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hsigma).app M ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId rho.source.toScheme).app Nb) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback rho.hom).mapIso
      ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
        (CategoryTheory.eqToIso (X.OX_toModules 1)))
  have hUθ := exists_not_isZeroAt_iso θ _ hU'
  rw [projectivizationMorphism_congr_iso _ _ θ _ hU' hUθ]
  refine projectivizationMorphism_congr_tuple _ (funext fun ℓ => ?_) hUθ hc'
  -- coordinatewise computation
  have h1 : ((AlgebraicGeometry.Scheme.Modules.pullbackComp sigma0 U.ι).app M).hom.app ⊤
      (sectionPullbackAlong sigma0 (sectionPullbackAlong U.ι (P ℓ))) =
      sectionPullbackAlong (sigma0 ≫ U.ι) (P ℓ) :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp sigma0 U.ι (P ℓ)
  have h2 : ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hsigma).app M).hom.app ⊤
      (sectionPullbackAlong (sigma0 ≫ U.ι) (P ℓ)) =
      sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules) (P ℓ) :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply hsigma (P ℓ)
  have h3 : ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId rho.source.toScheme).app Nb).hom.app ⊤
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection L.toModules) (P ℓ)) =
      AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ) := rfl
  have h4 : ∀ c, ((AlgebraicGeometry.Scheme.Modules.pullback rho.hom).map
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1)))).app ⊤
        (sectionPullbackAlong rho.hom
          ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom c)) =
      sectionPullbackAlong rho.hom c := by
    intro c
    have hn := sectionPullbackAlong_naturality rho.hom
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1)))
      ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom c)
    refine hn.symm.trans ?_
    congr 1
    change (((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1))).val.app (Opposite.op ⊤)).hom c = c
    rw [← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl, CategoryTheory.Functor.map_id]
    rfl
  change ((AlgebraicGeometry.Scheme.Modules.pullback rho.hom).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1)))).app ⊤
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app Nb ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId rho.source.toScheme).app Nb).hom.app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hsigma).app M).hom.app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp sigma0 U.ι).app M).hom.app ⊤
          (sectionPullbackAlong sigma0 (sectionPullbackAlong U.ι (P ℓ)))))) =
    sectionPullbackAlong rho.hom (D.coord ℓ)
  rw [h1, h2, h3, hzero ℓ]
  exact h4 (D.coord ℓ)

end
