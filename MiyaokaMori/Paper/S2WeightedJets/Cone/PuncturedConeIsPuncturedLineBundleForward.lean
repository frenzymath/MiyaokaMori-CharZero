import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractSurjective
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductTwistIso
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceHomIsZeroAtOfMemRangeZeroSection

/-! # The forward morphism from the punctured cone to the punctured line bundle

"A nonzero vector determines a point of `X`": there is a morphism `α : Z^× → Tot(L)^×` over `C ×_k X`
whose corresponding section `w_α ∈ Γ(Z^×, g^*L)` satisfies `⟨w_α, g^*pr₂^*(e^*x_i)⟩ = z_i`
(`IsConeToTotalSpaceHom`) (eq. (2.1) of the paper).

Assembly from three lemmas:
* `puncturedConeToProduct.exists_twistIso`: `θ : g^*pr₂^*O_X(1) ≅ g^*pr₁^*A` with
  `θ(g^*pr₂^*(e^*x_i)) = z_i`;
* `conePuncturedLineBundle.exists_contractSections_eq`: surjectivity of the pairing — for every
  `ψ : g^*pr₂^*O_X(1) ⟶ g^*pr₁^*A` there is `w ∈ Γ(Z^×, g^*L)` with `⟨w, q⟩ = ψ(q)`; together with
  `conePuncturedLineBundle.isZeroAt_contractSections` (if `w` vanishes at `p`, so does `⟨w, q⟩`);
* `AlgebraicGeometry.Scheme.isZeroAt_totalSpaceHomEquiv_of_mem_range_zeroSection`: if `m(p)` lies in the
  image of the zero section, the corresponding section vanishes at `p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Transport of `IsZeroAt` back along a two-step section-retraction: if `f₁ ≫ f₂ ≫ g = 𝟙 M` and
`f₂(f₁(s))` is zero at `x`, then `s` is zero at `x` (apply `isZeroAt_map g` and cancel). The hypothesis is
spelled with `Hom.app _ ⊤`; the cancellation `g(f₂(f₁(s))) = s` is a `congrArg` on `f₁ ≫ f₂ ≫ g = 𝟙`, cheap
because `M`, `N`, `P` are abstract (the same defeq on concrete pullback functors times out). -/
theorem isZeroAt_of_isZeroAt_app_app_of_comp_eq_id {X : AlgebraicGeometry.Scheme.{u}} {M N P : X.Modules}
    (f₁ : M ⟶ N) (f₂ : N ⟶ P) (g : P ⟶ M) (hfg : f₁ ≫ f₂ ≫ g = 𝟙 M)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : IsZeroAt ((f₂.app ⊤) ((f₁.app ⊤) s)) x) : IsZeroAt s x := by
  have h2 := isZeroAt_map g _ x h
  have e : (g.val.app (Opposite.op ⊤)).hom ((f₂.app ⊤) ((f₁.app ⊤) s)) = s :=
    congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom s) hfg
  rw [e] at h2
  exact h2

/-- `IsZeroAt` is transported back along the round trip `H.obj A → G.obj A → F.obj A` given by two natural
isomorphisms `Ξ : H ≅ G`, `Θ : F ≅ G`: if `Θ⁻¹(Ξ(s))` is zero at `x` then so is `s`. Everything is implicit and
gets assigned syntactically from `h`; this is how `puncturedConeToProduct.coordOverProduct` (which is literally
`(pullbackComp g pr₁).inv.app A |>.app ⊤ ((pullbackCongr comp_fst.symm).hom.app A |>.app ⊤ (coord i))`) is undone
without ever re-elaborating the concrete pullback functors (that unification times out). -/
theorem isZeroAt_of_isZeroAt_natIso_inv_app_hom_app {X : AlgebraicGeometry.Scheme.{u}} {C' : Type v}
    [CategoryTheory.Category.{w} C'] {F G H : C' ⥤ X.Modules} {Θ : F ≅ G} {Ξ : H ≅ G} {A : C'}
    {s : ((H.obj A).val.obj (Opposite.op ⊤) : Type u)} {x : X}
    (h : IsZeroAt (((Θ.inv.app A).app ⊤) (((Ξ.hom.app A).app ⊤) s)) x) : IsZeroAt s x := by
  have hcomp : Ξ.hom.app A ≫ Θ.inv.app A ≫ Θ.hom.app A ≫ Ξ.inv.app A = 𝟙 _ := by
    rw [Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app]
  exact isZeroAt_of_isZeroAt_app_app_of_comp_eq_id (Ξ.hom.app A) (Θ.inv.app A) (Θ.hom.app A ≫ Ξ.inv.app A)
    hcomp s x h

/-- There is an `α : Z^× → Tot(L)^×` satisfying the forward characterising property.

Source: eq. (2.1) of the paper ("a nonzero vector determines a point of `X`");
Stacks 01NE (morphisms to `P^N` ↔ a line bundle with generating sections); Stacks 01CT (for line bundles,
`M ⊗ Q^∨ ≅ 𝓗om(Q, M)`).

Notation: `W := Z^×`, `t := puncturedConeToProduct.base` (`W → C`), `z_i := puncturedConeToProduct.coord ∈ Γ(W, t^*A)`,
`φ := projectivizationMorphism (t^*A) z` (`W → P^N`), `Φ := puncturedConeToProduct.toX` (`Φ ≫ e.emb = φ`,
`IsClosedImmersion.lift_fac`), `g := puncturedConeToProduct = pullback.lift t Φ`, `L := conePuncturedLineBundle e A`,
`q_i := conePuncturedLineBundle.coordinate = pr₂^*(e^*x_i)`.

Proof:
1. `puncturedConeToProduct.exists_twistIso` gives `θ : g^*pr₂^*O_X(1) ≅ g^*pr₁^*A` with `θ(g^*q_i) = z_i`
   (`coordOverProduct`).
2. `conePuncturedLineBundle.exists_contractSections_eq` for `T = Over.mk g`, `ψ = θ.hom` gives `w ∈ Γ(W, g^*L)`
   with `⟨w, q⟩ = θ(q)` for all `q`; in particular `⟨w, g^*q_i⟩ = z_i`.
3. `w` is nowhere zero: if `w` vanished at `p`, then `⟨w, g^*q_ℓ⟩ = z_ℓ` would vanish at `p`
   (`isZeroAt_contractSections`, transported back to `Γ(W, t^*A)` by the inverses of
   `pullbackComp`/`pullbackCongr`, `isZeroAt_map`), contradicting `coord_nowhereZero`.
4. `α₀ := (totalSpaceHomEquiv L (Over.mk g)).symm w : Over.mk g ⟶ totalSpace L`; if `α₀(p)` lay in the image of the
   zero section, `w` would vanish at `p` (`isZeroAt_totalSpaceHomEquiv_of_mem_range_zeroSection`), so
   `range α₀.left ⊆ (range (zeroSection L))ᶜ = totalSpacePunctured L`; take `α := IsOpenImmersion.lift ι α₀.left`.
5. `α ≫ ι = α₀.left` (`lift_fac`), hence `α ≫ toBase = g` (`Over.w`); `Over.homMk (α ≫ ι) _ = α₀`
   (`Over.OverMorphism.ext`), whose `totalSpaceHomEquiv` is `w`, and step 2 gives the identities for all `i`. -/
theorem puncturedCone_exists_isConeToTotalSpaceHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ∃ α : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme ⟶ (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme,
      IsConeToTotalSpaceHom e E A hdeg α := by
  obtain ⟨ψ, hψ⟩ := puncturedConeToProduct.exists_twistIso e E A hdeg
  obtain ⟨w, hw⟩ := conePuncturedLineBundle.exists_contractSections_eq e A
    (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg)) ψ.hom
  -- Step 3: `w` is nowhere zero.
  have hwnz : ∀ p : (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme, ¬ IsZeroAt w p := by
    intro p hp
    obtain ⟨ℓ, hℓ⟩ := puncturedConeToProduct.coord_nowhereZero e E A hdeg p
    apply hℓ
    have h1 := conePuncturedLineBundle.isZeroAt_contractSections e A
      (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg)) w
      (sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e ℓ)) p hp
    rw [hw, hψ] at h1
    unfold puncturedConeToProduct.coordOverProduct at h1
    -- `coordOverProduct ℓ = Θ.inv (Ξ.hom (coord ℓ))` with Θ = pullbackComp g pr₁, Ξ = pullbackCongr comp_fst.symm;
    -- undo the round trip. The isomorphisms are picked out of `h1` by unification (see the helper's docstring).
    exact isZeroAt_of_isZeroAt_natIso_inv_app_hom_app h1
  -- Step 4: the morphism `α₀ : Z^× → Tot(L)` over `C ×_k X`, avoiding the zero section.
  let α₀ := (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (conePuncturedLineBundle e A)
    (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg))).symm w
  have hα₀ : AlgebraicGeometry.Scheme.totalSpaceHomEquiv (conePuncturedLineBundle e A)
      (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg)) α₀ = w :=
    Equiv.apply_symm_apply _ _
  have hrange : Set.range α₀.left ⊆
      Set.range (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    show α₀.left.base p ∈ (Set.range (AlgebraicGeometry.Scheme.zeroSection (conePuncturedLineBundle e A)).base)ᶜ
    intro hmem
    apply hwnz p
    rw [← hα₀]
    exact AlgebraicGeometry.Scheme.isZeroAt_totalSpaceHomEquiv_of_mem_range_zeroSection
      (conePuncturedLineBundle e A) (puncturedConeToProduct e E A hdeg) α₀ p hmem
  refine ⟨AlgebraicGeometry.IsOpenImmersion.lift
    (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι α₀.left hrange, ?_⟩
  have hfac : AlgebraicGeometry.IsOpenImmersion.lift
      (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι α₀.left hrange ≫
      (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι = α₀.left :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hα : AlgebraicGeometry.IsOpenImmersion.lift
      (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).ι α₀.left hrange ≫
      AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A) =
      puncturedConeToProduct e E A hdeg := by
    unfold AlgebraicGeometry.Scheme.totalSpacePunctured.toBase
    rw [← Category.assoc, hfac]
    exact CategoryTheory.Over.w α₀
  refine ⟨hα, fun i => ?_⟩
  -- Step 5: the morphism `Over.homMk (α ≫ ι)` is `α₀`, whose section is `w`.
  have key : ∀ m : CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg) ⟶
      AlgebraicGeometry.Scheme.totalSpace (conePuncturedLineBundle e A), m = α₀ →
      conePuncturedLineBundle.contractSections e A (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg))
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (conePuncturedLineBundle e A)
          (CategoryTheory.Over.mk (puncturedConeToProduct e E A hdeg)) m)
        (sectionPullbackAlong (puncturedConeToProduct e E A hdeg) (conePuncturedLineBundle.coordinate C e i)) =
      puncturedConeToProduct.coordOverProduct e E A hdeg i := by
    intro m hm
    rw [hm, hα₀, hw, hψ]
  exact key _ (CategoryTheory.Over.OverMorphism.ext hfac)

end
