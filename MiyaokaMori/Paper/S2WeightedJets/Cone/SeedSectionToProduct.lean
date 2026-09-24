import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProduct
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMorphismCongrIso

/-! # The seed section composed with the projection to `C × X`

The seed section composed with `𝒵^× → C ×_k X` is `(𝟙_C, f)`: the point of `X` defined by the
nonzero vector `(f_0(c), …, f_N(c))` is `f(c)` (§2.1 of the paper: `p ∘ s = (id_C, f)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Step (b) of the proof, general form: for `m : T ⟶ Tot(V)` with associated section
`z = totalSpaceHomEquiv V T m ∈ Γ(T, T.hom^*V)`, a component map `g : V ⟶ B`, and `j : S ⟶ T.left`,
pulling the component `(T.hom^*g)(z)` back along `j` and passing through `pullbackComp` gives the
component of the section associated with `j ≫ m`. Direct from `totalSpaceHomEquiv_naturality`,
the naturality of `pullbackComp` in the module, and
the naturality of `sectionPullbackAlong` (`AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality`). -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_map_sectionPullbackAlong
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace V)
    {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left) {B : X.Modules} (g : V ⟶ B) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app B).app ⊤
        (sectionPullbackAlong j (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map g).app ⊤
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m))) =
      ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ T.hom)).map g).app ⊤
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ T.hom))
          ((CategoryTheory.Over.homMk j rfl : CategoryTheory.Over.mk (j ≫ T.hom) ⟶ T) ≫ m)) := by
  rw [AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality]
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality j
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map g)
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m)
  have h2 := congrArg (fun ψ => ψ.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback j
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T m)))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.naturality g)
  refine Eq.trans (congrArg
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app B).app ⊤) h1.symm) ?_
  exact h2

/-- Step (b) of the proof, identity case: when `q = 𝟙 X` and `σ ≫ p = q`, the section
`totalSpaceHomEquiv V (Over.mk q) σ ∈ Γ(X, q^*V)` is carried by an isomorphism `q^*B ≅ B`
(the identity-pullback iso `pullbackId`) to the corresponding section of `Γ(X, V)`, compatibly
with any component map `g : V ⟶ B`. Proof: `subst`, then naturality of `pullbackId`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_exists_iso_of_eq_id
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (q : X ⟶ X) (hq : q = 𝟙 X) (σ : X ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (hσ : σ ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = q) (B : X.Modules) :
    ∃ θ : (AlgebraicGeometry.Scheme.Modules.pullback q).obj B ≅ B, ∀ g : V ⟶ B,
      θ.hom.app ⊤ (((AlgebraicGeometry.Scheme.Modules.pullback q).map g).app ⊤
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk q)
          (CategoryTheory.Over.homMk σ hσ))) =
      g.app ⊤ (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app V).app ⊤
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 X))
          (CategoryTheory.Over.homMk σ (hσ.trans hq)))) := by
  subst hq
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pullbackId X).app B, fun g => ?_⟩
  have hnat := (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.naturality g
  have := congrArg (fun ψ => ψ.app ⊤
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 X))
      (CategoryTheory.Over.homMk σ hσ))) hnat
  exact this


/-- Step (b) of the proof: with `t : W = Z^× → C` the base map and
`z_ℓ ∈ Γ(W, t^*A)` the coordinates of `W ↪ Tot(A^{⊕(N+1)})` (`puncturedConeToProduct.coord`), the seed
section `s' : C → W` satisfies `s' ≫ t = 𝟙_C`, so `s'^*t^*A ≅ A`, and under this isomorphism
`s'^*z_ℓ = coord ℓ`: the seed section is built from `coord` through `totalSpaceSectionEquiv`, and
`totalSpaceHomEquiv` is natural in the source (`totalSpaceHomEquiv_naturality`), so pulling the
coordinate section of `W ↪ Tot` back along `s'` gives the coordinate section of `s' ≫ (W ↪ Tot) = σ_coord`. -/
theorem seedSection_exists_iso_sectionPullbackAlong_coord {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (hdeg : ∀ j, 0 < E.deg j)
    (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0)
    (s' : C ⟶ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).toScheme)
    (hs' : s' ≫ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).ι =
      (seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish).1) :
    ∃ θ : (AlgebraicGeometry.Scheme.Modules.pullback s').obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (puncturedConeToProduct.base e E (seedLineBundle e f) hdeg)).obj (seedLineBundle e f)) ≅
        seedLineBundle e f,
      ∀ ℓ, θ.hom.app ⊤ (sectionPullbackAlong s'
        (puncturedConeToProduct.coord e E (seedLineBundle e f) hdeg ℓ)) = coord ℓ := by
  let A := seedLineBundle e f
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let t := puncturedConeToProduct.base e E A hdeg
  let T := CategoryTheory.Over.mk t
  let m := puncturedConeToProduct.toTot e E A hdeg
  let I : (AlgebraicGeometry.Scheme.totalSpace V).left.IdealSheafData :=
    ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
  let σ := seedSection.totSection A N coord
  let s := seedSection A N coord E.deg E.F E.homogeneous hvanish
  let t0 : (V.val.obj (Opposite.op ⊤) : Type u) := ∑ i : Fin (N + 1),
    ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i).val.app (Opposite.op ⊤)).hom
      (coord i)
  have hs1 : s.1 ≫ I.subschemeι = σ.1 :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι σ.1 (by
      simp only [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
      exact seedSection.ideal_le_ker A N coord E.deg E.F E.homogeneous hvanish)
  have hst : s' ≫ t = 𝟙 C := by
    change s' ≫ ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
      (twistedAffineCone A N E.deg E.F E.homogeneous).hom) = 𝟙 C
    rw [← Category.assoc, hs']
    exact s.2
  have hσm : s' ≫ m.left = σ.1 :=
    (Category.assoc s' (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι I.subschemeι).symm.trans
      ((congrArg (fun g => g ≫ I.subschemeι) hs').trans hs1)
  have hσ' : σ.1 ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = s' ≫ t := σ.2.trans hst.symm
  obtain ⟨θ₂, hθ₂⟩ :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_exists_iso_of_eq_id V (s' ≫ t) hst σ.1 hσ' A
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pullbackComp s' t).app A ≪≫ θ₂, fun ℓ => ?_⟩
  have h1 := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_map_sectionPullbackAlong V T m s'
    (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)
  have hm : (CategoryTheory.Over.homMk s' rfl : CategoryTheory.Over.mk (s' ≫ T.hom) ⟶ T) ≫ m =
      CategoryTheory.Over.homMk σ.1 hσ' := by
    ext
    exact hσm
  rw [hm] at h1
  have h2 := hθ₂ (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)
  have hdef : (CategoryTheory.Over.homMk σ.1 (hσ'.trans hst) :
      CategoryTheory.Over.mk (𝟙 C) ⟶ AlgebraicGeometry.Scheme.totalSpace V) =
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 C))).symm
        ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom t0) :=
    rfl
  rw [hdef, Equiv.apply_symm_apply] at h2
  have hinv : (((AlgebraicGeometry.Scheme.Modules.pullbackId C).hom.app V).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom t0) = t0 :=
    congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom t0)
      ((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv_hom_id_app V)
  have hπ : ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ).val.app
      (Opposite.op ⊤)).hom t0 = coord ℓ := by
    change ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ).val.app
      (Opposite.op ⊤)).hom (∑ j : Fin (N + 1),
        ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) j).val.app
          (Opposite.op ⊤)).hom (coord j)) = coord ℓ
    rw [map_sum, Finset.sum_eq_single ℓ]
    · exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (coord ℓ))
        (CategoryTheory.Limits.biproduct.ι_π_self (fun _ : Fin (N + 1) => A) ℓ)
    · intro j _ hj
      exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (coord j))
        (CategoryTheory.Limits.biproduct.ι_π_ne (fun _ : Fin (N + 1) => A) hj)
    · intro h
      exact absurd (Finset.mem_univ ℓ) h
  have h3 : ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ).app ⊤)
      ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).hom.app V).app ⊤)
        ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom t0))
      = coord ℓ := by
    refine Eq.trans (congrArg ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ).app ⊤)
      hinv) ?_
    exact hπ
  rw [CategoryTheory.Iso.trans_hom, AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
  refine Eq.trans (congrArg (θ₂.hom.app ⊤) h1) ?_
  exact h2.trans h3

/-- **The seed section lifts the graph of `f`** (§2.1 of the paper: `p ∘ s = (id_C, f)`): the seed
section `s' : C → Z^×`, followed by `Z^× → C ×_k X` (`puncturedConeToProduct`), is the graph `(𝟙_C, f)`.

Proof (four steps). By `pullback.hom_ext` compare the two components.
* `C`-component: `puncturedConeToProduct ≫ pr₁ = t := (Z^× ↪ Z) ≫ (Z → C)`, and
  `s' ≫ t = s ≫ (Z → C) = 𝟙_C` because `s' ≫ ι = s` (`hs'`) and `s` is a section (`seedSection`).
* `X`-component: `e.emb` is a closed immersion, hence mono, so it suffices to compare after `e.emb`.
  `toX ≫ e.emb = φ := projectivizationMorphism (t^*A) z` (`IsClosedImmersion.lift_fac`); by
  `projectivizationMorphism_pullback`, `s' ≫ φ = projectivizationMorphism (s'^*t^*A) (s'^*z)`; by
  `seedSection_exists_iso_sectionPullbackAlong_coord` there is `θ : s'^*t^*A ≅ A` with `θ(s'^*z_ℓ) = coord ℓ`,
  so `projectivizationMorphism_congr_iso` turns this into `projectivizationMorphism A coord`, which is
  `f ≫ e.emb` by the second component of `hcoord`. -/
theorem seedSection_comp_puncturedConeToProduct {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (hdeg : ∀ j, 0 < E.deg j)
    (f : C ⟶ X) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0)
    (s' : C ⟶ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).toScheme)
    (hs' : s' ≫ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).ι =
      (seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish).1) :
    s' ≫ puncturedConeToProduct e E (seedLineBundle e f) hdeg =
      CategoryTheory.Limits.pullback.lift (CategoryTheory.CategoryStruct.id C) f (by simp) := by
  let A := seedLineBundle e f
  let t := puncturedConeToProduct.base e E A hdeg
  have hst : s' ≫ t = 𝟙 C := by
    change s' ≫ ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
      (twistedAffineCone A N E.deg E.F E.homogeneous).hom) = 𝟙 C
    rw [← Category.assoc, hs']
    exact (seedSection A N coord E.deg E.F E.homogeneous hvanish).2
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [Category.assoc, CategoryTheory.Limits.pullback.lift_fst]
    change s' ≫ CategoryTheory.Limits.pullback.lift (puncturedConeToProduct.base e E A hdeg)
      (puncturedConeToProduct.toX e E A hdeg) (puncturedConeToProduct.base_comp e E A hdeg) ≫ _ = _
    rw [CategoryTheory.Limits.pullback.lift_fst]
    exact hst
  · rw [Category.assoc, CategoryTheory.Limits.pullback.lift_snd]
    change s' ≫ CategoryTheory.Limits.pullback.lift (puncturedConeToProduct.base e E A hdeg)
      (puncturedConeToProduct.toX e E A hdeg) (puncturedConeToProduct.base_comp e E A hdeg) ≫ _ = _
    rw [CategoryTheory.Limits.pullback.lift_snd, ← cancel_mono e.emb]
    obtain ⟨h, hproj⟩ := hcoord
    rw [Category.assoc, ← hproj]
    let _ := puncturedConeToProduct.overK e E A hdeg
    have : s'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
      change s' ≫ (t ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) = _
      rw [← Category.assoc, hst, Category.id_comp]⟩
    have hlift := AlgebraicGeometry.IsClosedImmersion.lift_fac e.emb _
      (puncturedConeToProduct.emb_ker_le e E A hdeg)
    change s' ≫ AlgebraicGeometry.IsClosedImmersion.lift e.emb _
      (puncturedConeToProduct.emb_ker_le e E A hdeg) ≫ e.emb = _
    rw [hlift]
    have hz' : ∀ c : C, ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong s'
        (puncturedConeToProduct.coord e E A hdeg ℓ)) c := fun c => by
      obtain ⟨ℓ, hℓ⟩ := puncturedConeToProduct.coord_nowhereZero e E A hdeg (s'.base c)
      exact ⟨ℓ, not_isZeroAt_sectionPullbackAlong s' _ _ c hℓ⟩
    rw [projectivizationMorphism_pullback s' _ (puncturedConeToProduct.coord e E A hdeg)
      (puncturedConeToProduct.coord_nowhereZero e E A hdeg) hz']
    obtain ⟨θ, hθ⟩ := seedSection_exists_iso_sectionPullbackAlong_coord e E hdeg f coord hvanish s' hs'
    rw [projectivizationMorphism_congr_iso _ A θ _ hz' (exists_not_isZeroAt_iso θ _ hz')]
    have key : ∀ (P Q : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (hPQ : P = Q)
        (hP : ∀ c : C, ∃ ℓ, ¬ IsZeroAt (P ℓ) c) (hQ : ∀ c : C, ∃ ℓ, ¬ IsZeroAt (Q ℓ) c),
        projectivizationMorphism (k := k) A P hP = projectivizationMorphism (k := k) A Q hQ := by
      intro P Q hPQ hP hQ
      subst hPQ
      rfl
    exact key _ _ (funext hθ) _ _

end
