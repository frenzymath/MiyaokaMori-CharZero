import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeContainsZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeOpen
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivNaturality
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # The seed section lies in the punctured cone

The seed section `s` lands in `𝒵^×`, because `f_0, …, f_N` have no common zero (§2.1 of the paper:
"the sections `f_i` … have no common zero, so their tuple gives a section of `𝒵^× → C`").

Proof:
* `Z^×` is the open complement of the image of the vertex section `σ₀ : C → Z` (the zero section
  lifted along the closed immersion `ι_Z`) (`puncturedCone`). To lift `s` to `Z^×` it suffices, by
  `IsOpenImmersion.lift`, that the image lies in `Z^×`, i.e. `s(c) ∉ σ₀(C)` for every `c ∈ C`.
* If `s(c) = σ₀(c')`, applying `ι_Z` gives `σ_f(c) = zeroSection(c')` (`σ_f = seedSection.totSection`,
  `s ≫ ι_Z = σ_f`), and applying the projection `p` gives `c = c'`. This reduces to
  `seedSection.totSection_apply_ne_zeroSection_apply`: `σ_f(c) ≠ zeroSection(c)` as soon as some
  `f_i` is nonzero at `c` (the first component of `hcoord`).
* The latter uses the tautological section `ξ = totalSpaceHomEquiv V Tot (𝟙)` on `Tot(V)`
  (`V = A^{⊕(N+1)}`): `zeroSection^* ξ = 0` (`sectionPullbackAlong_zeroSection_tautological`), so `ξ`
  vanishes at `zeroSection(c) = σ_f(c)`; pulling back along `σ_f`, `σ_f^* ξ` vanishes at `c`
  (`isZeroAt_sectionPullbackAlong_of_isZeroAt`: the adjunction unit on stalks is semilinear over a
  local homomorphism and sends `𝔪·M` into `𝔪·M`); by naturality `σ_f^* ξ` corresponds to the section
  `Σ_i ι_i(f_i)` associated with `σ_f` itself (an isomorphism of sheaves of modules preserves `IsZeroAt`:
  `isZeroAt_map`), and applying `biproduct.π_i` shows that `f_i` vanishes at `c`, a contradiction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A morphism of sheaves of modules preserves "vanishing at `x`": `φ : M ⟶ M'` is `O_{X,x}`-linear on
stalks (`AlgebraicGeometry.Scheme.Modules.moduleStalkMap`), hence sends `𝔪_x·M_x` into `𝔪_x·M'_x`. -/
theorem isZeroAt_map {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules} (φ : M ⟶ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) (h : IsZeroAt s x) :
    IsZeroAt ((φ.val.app (Opposite.op ⊤)).hom s) x :=
  Stacks01ne.isZeroAt_map_hom φ s x h

/-- If a section vanishes at `g(x)`, the pulled-back section vanishes at `x` (for any sheaf of modules):
the germ of the pulled-back section is the adjunction unit applied to the original germ
(`modulePullbackStalkUnitAddHom_germ`), the unit is semilinear over the local homomorphism `g^♯_x`, and a
local homomorphism sends `𝔪_{g x}` into `𝔪_x` (`map_nonunit`). -/
theorem isZeroAt_sectionPullbackAlong_of_isZeroAt {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : IsZeroAt s (g.base x)) : IsZeroAt (sectionPullbackAlong g s) x :=
  Stacks01ne.isZeroAt_pullback g M s x h

/-- The tautological section `ξ = totalSpaceHomEquiv V Tot(V) (𝟙) ∈ Γ(Tot V, p^*V)` pulls back to zero
along the zero section (the version of `tautologicalSection_zeroSection` for general sheaves of modules;
same proof). -/
theorem AlgebraicGeometry.Scheme.sectionPullbackAlong_zeroSection_tautological
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V)
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (AlgebraicGeometry.Scheme.totalSpace V)
        (CategoryTheory.CategoryStruct.id _)) = 0 :=
  AlgebraicGeometry.Scheme.zeroSection_pullback_tautologicalSection_eq_zero V

/-- Transport along `q = 𝟙`: the section–morphism correspondences on `Over.mk q` and `Over.mk (𝟙 X)` give
the same `IsZeroAt` (`subst`). -/
theorem isZeroAt_totalSpaceHomEquiv_of_eq_id {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (q : X ⟶ X) (hq : q = 𝟙 X) (σ : X ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (hσ : σ ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = q) (x : X)
    (h : IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk q)
      (CategoryTheory.Over.homMk σ hσ)) x) :
    IsZeroAt (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 X))
      (CategoryTheory.Over.homMk σ (hσ.trans hq))) x := by
  subst hq
  exact h

/-- The core: if some `f_i` is nonzero at `c`, then `σ_f(c) ≠ zeroSection(c)` (`σ_f = seedSection.totSection`). -/
theorem seedSection.totSection_apply_ne_zeroSection_apply {C : AlgebraicGeometry.Scheme.{u}}
    (A : C.Modules) [A.IsLineBundle] (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    (c : C) (i : Fin (N + 1)) (hi : ¬ IsZeroAt (f i) c) :
    (seedSection.totSection A N f).1 c ≠
      AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) c := by
  intro heq
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let σf : C ⟶ T.left := (seedSection.totSection A N f).1
  have hσ : σf ≫ T.hom = 𝟙 C := (seedSection.totSection A N f).2
  let ξ := AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (𝟙 T)
  let t0 : (V.val.obj (Opposite.op ⊤) : Type u) := ∑ j : Fin (N + 1),
    ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) j).val.app (Opposite.op ⊤)).hom (f j)
  have h1 : IsZeroAt ξ (AlgebraicGeometry.Scheme.zeroSection V c) :=
    isZeroAt_of_sectionPullbackAlong_eq_zero _ _ ξ c
      (AlgebraicGeometry.Scheme.sectionPullbackAlong_zeroSection_tautological V)
  have h2 : IsZeroAt ξ (σf c) := by
    change IsZeroAt ξ ((seedSection.totSection A N f).1 c)
    rw [heq]
    exact h1
  have h3 : IsZeroAt (sectionPullbackAlong σf ξ) c :=
    isZeroAt_sectionPullbackAlong_of_isZeroAt σf _ ξ c h2
  have h4 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullbackComp σf T.hom).hom.app V) _ c h3
  have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V T σf (𝟙 T)
  rw [Category.comp_id] at hn
  rw [← hn] at h4
  have h5 := isZeroAt_totalSpaceHomEquiv_of_eq_id V (σf ≫ T.hom) hσ σf rfl c h4
  have hdef : (CategoryTheory.Over.homMk σf (rfl.trans hσ) : CategoryTheory.Over.mk (𝟙 C) ⟶ T) =
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 C))).symm
        ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom t0) :=
    rfl
  rw [hdef, Equiv.apply_symm_apply] at h5
  have h6 := isZeroAt_map ((AlgebraicGeometry.Scheme.Modules.pullbackId C).hom.app V) _ c h5
  have hinv : (((AlgebraicGeometry.Scheme.Modules.pullbackId C).hom.app V).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom t0) = t0 :=
    congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom t0)
      ((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv_hom_id_app V)
  rw [hinv] at h6
  have h7 := isZeroAt_map (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i) _ c h6
  have hπ : ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i).val.app
      (Opposite.op ⊤)).hom t0 = f i := by
    change ((CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i).val.app
      (Opposite.op ⊤)).hom (∑ j : Fin (N + 1),
        ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) j).val.app (Opposite.op ⊤)).hom (f j)) = f i
    rw [map_sum, Finset.sum_eq_single i]
    · exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (f i))
        (CategoryTheory.Limits.biproduct.ι_π_self (fun _ : Fin (N + 1) => A) i)
    · intro j _ hj
      exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (f j))
        (CategoryTheory.Limits.biproduct.ι_π_ne (fun _ : Fin (N + 1) => A) hj)
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hπ] at h7
  exact hi h7


theorem seedSection_mem_punctured {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (f : C ⟶ X)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord) (hdeg : ∀ j, 0 < E.deg j)
    (hvanish : ∀ j, evalHomogeneousAtSections (seedLineBundle e f) (E.F j) (E.homogeneous j) coord = 0) :
    ∃ s' : C ⟶ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).toScheme,
      s' ≫ (puncturedCone (seedLineBundle e f) N E.deg hdeg E.F E.homogeneous).ι =
        (seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous hvanish).1 := by
  obtain ⟨hnz, -⟩ := hcoord
  let A := seedLineBundle e f
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let I : (AlgebraicGeometry.Scheme.totalSpace V).left.IdealSheafData :=
    ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _ (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
  let s := seedSection A N coord E.deg E.F E.homogeneous hvanish
  let U := puncturedCone A N E.deg hdeg E.F E.homogeneous
  have hs1 : s.1 ≫ I.subschemeι = (seedSection.totSection A N coord).1 :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι (seedSection.totSection A N coord).1
      (by
        simp only [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
        exact seedSection.ideal_le_ker A N coord E.deg E.F E.homogeneous hvanish)
  let σ0 : C ⟶ (twistedAffineCone A N E.deg E.F E.homogeneous).left :=
    (AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) (by
        obtain ⟨τ, hτ⟩ := zeroSection_mem_twistedAffineCone A N E.deg hdeg E.F E.homogeneous
        rw [← hτ]
        exact AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _) : C ⟶ I.subscheme)
  have hσ0 : σ0 ≫ I.subschemeι = AlgebraicGeometry.Scheme.zeroSection V :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) _
  have hrange : Set.range s.1 ⊆ Set.range U.ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    obtain ⟨i, hi⟩ := hnz c
    rintro ⟨c', hc'⟩
    have hc'' : σ0 c' = s.1 c := hc'
    have h1 : (σ0 ≫ I.subschemeι) c' = (s.1 ≫ I.subschemeι) c :=
      congrArg (fun z => I.subschemeι z) hc''
    rw [hσ0, hs1] at h1
    have h2 : (AlgebraicGeometry.Scheme.zeroSection V ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) c' =
        ((seedSection.totSection A N coord).1 ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom) c :=
      congrArg (fun z => (AlgebraicGeometry.Scheme.totalSpace V).hom z) h1
    rw [AlgebraicGeometry.Scheme.zeroSection_comp, (seedSection.totSection A N coord).2] at h2
    have h2' : c' = c := h2
    rw [h2'] at h1
    exact seedSection.totSection_apply_ne_zeroSection_apply A N coord c i hi h1.symm
  exact ⟨AlgebraicGeometry.IsOpenImmersion.lift U.ι s.1 hrange,
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩

end
