import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackwardCoord
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackwardTransportTwo
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMorphismCongrIso
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSectionCompat

/-! # The backward morphism from the punctured line bundle to the punctured cone

There is a morphism `β : Tot(L)^× → Z^×` over `C ×_k X` whose pulled-back coordinates `β^*z_i` equal
the pairing of the tautological section with `pr₂^*(e^*x_i)` (`IsTotalSpaceToConeHom`)
(eq. (2.1) of the paper: "a nonzero tensor over `(c, x)` is sent to the
corresponding nonzero vector in `A_c^{⊕(N+1)}`").

## Skeleton

Notation (namespace `puncturedTotalSpaceToCone`): `T× := Tot(L)^×` (`L := conePuncturedLineBundle e A` on
`C ×_k X`), `π := totalSpacePunctured.toBase L : T× → C ×_k X`, `t' := base e A = π ≫ pr₁`,
`x' := toX e A = π ≫ pr₂`, `w := tautologicalSection L ∈ Γ(T×, π^*L)`, `q_i := coordinate C e i = pr₂^*(e^*x_i)`,
`z_i := coordZ e A i = ⟨w, π^*q_i⟩ ∈ Γ(T×, π^*pr₁^*A)` and `z'_i := coord e A i ∈ Γ(T×, t'^*A)` its transport
along `pullbackComp`. `V := A^{⊕(N+1)}`, `p : Tot(V) → C`, `I := coneIdeal e E A = ⨆_j I(F_j(τ))` the ideal sheaf
of the cone `Z ⊆ Tot(V)`, `W := Z^× = puncturedCone …`.

Construction of `β = hom e E A hdeg`:
1. `toTot : Over.mk t' ⟶ Tot(V)` is the `C`-morphism with coordinates `z'` (`totalSpaceHomEquiv.symm (Σ ι_i z'_i)`;
   `toTot_coord`).
2. `F_j(z') = 0` (`eval_coord_eq_zero`) ⇒ `I ≤ ker toTot.left` (`toTot_left_ker`, via the T-point form of
   Stacks 02OR `sectionPullbackAlong_homogeneousEquationSection_eq_zero_iff`, proved here) ⇒
   `toCone : T× → Z` (`IsClosedImmersion.lift`).
3. `z'` nowhere all zero (`coord_nowhereZero`) ⇒ `toCone` avoids the vertex section (`range_toCone_subset`,
   proved here from `sectionPullbackAlong_zeroSection_tautological`) ⇒ `hom : T× → W` (`IsOpenImmersion.lift`).
4. `hom ≫ g = π` (`hom_comp_puncturedConeToProduct`): first component `hom_comp_base`, second component
   `hom_comp_toX` (`e.emb` is a monomorphism; `β ≫ φ_W = φ_{β^*z_W}` by `projectivizationMorphism_pullback`, and the
   transport `Θ` of `hom_pullback_coord` turns this into `φ_{z'} = x' ≫ e.emb` by `projectivizationMorphism_congr_iso`
   and `projectivizationMorphism_coord_eq`).
5. The coordinate identity of `IsTotalSpaceToConeHom` is `hom_isTotalSpaceToConeHom`: its
   first component is `hom_comp_puncturedConeToProduct`, the coordinate identity is `hom_pullback_coordZ`
   assembled by the two-spelling transport lemma `Modules.coordinate_transport_two` (`…BackwardTransportTwo`; see
   its module docstring for why the naive assembly is too slow).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## T-point form of Stacks 02OR for the cone equations -/

/-- **T-point form of Stacks 02OR for the cone equations.** For a `C`-morphism `j : S → Tot(A^{⊕(N+1)})`
over `b : S → C` (`j ≫ p = b`), the pullback `j^*(F(τ))` of the homogeneous equation section
`F(τ) = homogeneousEquationSection A N F hF` vanishes iff `F` evaluated
on the coordinates of the section of `b^*V` corresponding to `j` (`totalSpaceHomEquiv`) is zero. Here `S`
carries the `k`-structure `b ≫ (C ↘ Spec k)`.

Source: Definition 2.1 of the paper (`Z` is cut out by the `F_j(z)`), Stacks 02OR. Generalizes
`homogeneousEquationSection_le_ker_totalSpaceSection_iff` (the case `S = C`, `b = 𝟙`) and both directions of the
argument of `puncturedConeToProduct.eval_coord_eq_zero_aux`.

Proof: `subst`; `evalHomogeneousAtSections_pullback` along `j` gives
`θ_d(j^*F(τ)) = F(j^*τ_0, …, j^*τ_N)` (`θ_d = pullbackTensorPowIso`); the coordinates of `j` are the images of
`j^*τ_i` under `Θ = pullbackComp j p` (`totalSpaceHomEquiv_naturality_map`); `evalHomogeneousAtSections_iso Θ`
gives `Θ^{⊗d}(F(j^*τ)) = F(Θ ∘ j^*τ)`; isomorphisms preserve and reflect `= 0`
(`Modules.iso_hom_app_top_eq_zero_iff`). -/
theorem AlgebraicGeometry.Scheme.sectionPullbackAlong_homogeneousEquationSection_eq_zero_iff
    {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {d : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous d)
    {S : AlgebraicGeometry.Scheme.{u}} (b : S ⟶ C)
    (j : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left)
    (hb : j ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = b) :
    letI : S.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨b ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    sectionPullbackAlong j (homogeneousEquationSection A N F hF) = 0 ↔
      evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback b).obj A) F hF
        (fun i => (((AlgebraicGeometry.Scheme.Modules.pullback b).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j hb))) = 0 := by
  subst hb
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let p := T.hom
  letI instS : S.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(j ≫ p) ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI instT : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI hj : j.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    change j ≫ (p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      (j ≫ p) ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [Category.assoc]⟩
  let τ : Fin (N + 1) → (((AlgebraicGeometry.Scheme.Modules.pullback p).obj A).val.obj (Opposite.op ⊤) : Type u) :=
    fun i => (((AlgebraicGeometry.Scheme.Modules.pullback p).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (CategoryTheory.CategoryStruct.id T))
  have hFτ : homogeneousEquationSection A N F hF =
      evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF τ := rfl
  have hpull := evalHomogeneousAtSections_pullback (k := k) j
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF τ
  let Θ : (AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (j ≫ p)).obj A :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j p).app A
  have hcoord : (fun i => (((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ p)).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ p))
          (CategoryTheory.Over.homMk j rfl))) =
      fun i => ((Θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j (τ i))) := by
    funext i
    have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_map V
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i) T j (𝟙 T)
    rw [Category.comp_id] at hn
    exact hn
  have key1 : sectionPullbackAlong j (homogeneousEquationSection A N F hF) = 0 ↔
      evalHomogeneousAtSections
        ((AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
        F hF (fun i => sectionPullbackAlong j (τ i)) = 0 := by
    rw [← hpull, hFτ]
    exact (AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff _ _).symm
  have key2 : evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ p)).obj A) F hF
        (fun i => ((Θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j (τ i)))) = 0 ↔
      evalHomogeneousAtSections
        ((AlgebraicGeometry.Scheme.Modules.pullback j).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
        F hF (fun i => sectionPullbackAlong j (τ i)) = 0 := by
    rw [← evalHomogeneousAtSections_iso Θ F hF]
    exact AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff _ _
  rw [hcoord]
  exact key1.trans key2.symm

/-! ## Variable-level spelling lemmas (all schemes/modules are variables, so each is a cheap `rfl`; they are applied
at the concrete level only through `rw`/`exact` with syntactic matching — never through a defeq check under a
`DFunLike.coe` head, which unfolds `Modules.pullback` down to linear maps and costs > 45 s). -/

namespace AlgebraicGeometry.Scheme.Modules

/-- `Modules.Hom.app φ ⊤` applied to a global section is `(φ.val.app (op ⊤)).hom` applied to it (definitional). -/
theorem Hom.app_top_apply {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤) x = (φ.val.app (Opposite.op ⊤)).hom x := rfl

/-- `((α.app M).hom.val.app ⊤).hom = ((α.hom.app M).val.app ⊤).hom` for a natural isomorphism `α` (definitional). -/
theorem natIso_app_hom_val_app_apply {X Y : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules ⥤ Y.Modules}
    (α : F ≅ G) (M : X.Modules) (x : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((α.app M).hom.val.app (Opposite.op ⊤)).hom x) = ((α.hom.app M).val.app (Opposite.op ⊤)).hom x := rfl

/-- `IsZeroAt` is invariant under the component at `M` of a natural isomorphism, in the spelling
`((α.hom.app M).val.app ⊤).hom` (`isZeroAt_iso_iff'` for `α.app M`). -/
theorem isZeroAt_natIso_app_iff {X Y : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules ⥤ Y.Modules}
    (α : F ≅ G) (M : X.Modules) (s : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) (y : Y) :
    IsZeroAt (((α.hom.app M).val.app (Opposite.op ⊤)).hom s) y ↔ IsZeroAt s y :=
  isZeroAt_iso_iff' (α.app M) s y

end AlgebraicGeometry.Scheme.Modules

namespace puncturedTotalSpaceToCone

variable {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j)

/-! ## Notation: `base`, `toX`, `overK`, `coordZ`, `coord` and the two coordinate leaves `coord_nowhereZero`,
`eval_coord_eq_zero` live in `…BackwardCoord`. -/

/-- The ideal sheaf `I = ⨆_j I(F_j(τ))` of the cone `Z ⊆ Tot(A^{⊕(N+1)})` — the same term as inside
`twistedAffineCone` and `puncturedCone` (definitionally equal; named here so that instance search finds
`IsClosedImmersion I.subschemeι`). -/
def coneIdeal : (AlgebraicGeometry.Scheme.totalSpace
    (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left.IdealSheafData :=
  ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (E.F j) (E.homogeneous j))

/-! ## The morphism `Tot(L)^× → Tot(V) → Z → Z^×` -/

/-- The `C`-morphism `Tot(L)^× → Tot(A^{⊕(N+1)})` with coordinates `z'`. -/
def toTot : CategoryTheory.Over.mk (base e A) ⟶
    AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) :=
  (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
    (CategoryTheory.Over.mk (base e A))).symm
    (∑ i : Fin (N + 1), (((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
      (CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (coord e A i))

/-- The `i`-th coordinate of `toTot` is `z'_i`. -/
theorem toTot_coord (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (CategoryTheory.Over.mk (base e A)) (toTot e A)) = coord e A i := by
  have h0 : AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
      (CategoryTheory.Over.mk (base e A)) (toTot e A) =
      ∑ j : Fin (N + 1), (((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
        (CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) j)).val.app (Opposite.op ⊤)).hom
        (coord e A j) :=
    Equiv.apply_symm_apply _ _
  rw [h0, map_sum, Finset.sum_eq_single i]
  · have h : (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
          (CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i) = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, CategoryTheory.Limits.biproduct.ι_π_self,
        CategoryTheory.Functor.map_id]
    exact congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A =>
      (φ.val.app (Opposite.op ⊤)).hom (coord e A i)) h
  · intro j _ hj
    have h : (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
          (CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) j) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
          (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i) = 0 := by
      rw [← CategoryTheory.Functor.map_comp, CategoryTheory.Limits.biproduct.ι_π_ne _ hj,
        CategoryTheory.Functor.map_zero]
    exact (congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A =>
      (φ.val.app (Opposite.op ⊤)).hom (coord e A j)) h).trans rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The ideal sheaf of the cone `Z` is contained in the kernel of `toTot.left`: `toTot` lands in `Z`
(Stacks 02OR in its T-point form, from `eval_coord_eq_zero`). -/
theorem toTot_left_ker : coneIdeal e E A ≤ (toTot e A).left.ker := by
  unfold coneIdeal
  refine iSup_le fun j => ?_
  rw [AlgebraicGeometry.Scheme.idealSheafOfSection_le_ker_iff,
    AlgebraicGeometry.Scheme.sectionPullbackAlong_homogeneousEquationSection_eq_zero_iff A N (E.F j)
      (E.homogeneous j) (base e A) (toTot e A).left (CategoryTheory.Over.w (toTot e A))]
  have hm : (CategoryTheory.Over.homMk (toTot e A).left (CategoryTheory.Over.w (toTot e A)) :
      CategoryTheory.Over.mk (base e A) ⟶
        AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) = toTot e A :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [hm]
  have hc : (fun i => (((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (CategoryTheory.Over.mk (base e A)) (toTot e A))) = coord e A := funext (toTot_coord e A)
  rw [hc]
  exact eval_coord_eq_zero e E A j

/-- `Tot(L)^× → Z`, the lift of `toTot.left` through the closed immersion `Z ↪ Tot(V)`. -/
def toCone : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶
    (twistedAffineCone A N E.deg E.F E.homogeneous).left :=
  (AlgebraicGeometry.IsClosedImmersion.lift (coneIdeal e E A).subschemeι (toTot e A).left (by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
      exact toTot_left_ker e E A) :
    _ ⟶ (coneIdeal e E A).subscheme)

theorem toCone_comp_subschemeι :
    toCone e E A ≫ (coneIdeal e E A).subschemeι = (toTot e A).left :=
  AlgebraicGeometry.IsClosedImmersion.lift_fac (coneIdeal e E A).subschemeι (toTot e A).left _

/-- `toCone ≫ (Z → C) = t'`. -/
theorem toCone_comp_hom :
    toCone e E A ≫ (twistedAffineCone A N E.deg E.F E.homogeneous).hom = base e A := by
  have h : toCone e E A ≫ (twistedAffineCone A N E.deg E.F E.homogeneous).hom =
      (toCone e E A ≫ (coneIdeal e E A).subschemeι) ≫
        (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom :=
    (Category.assoc _ _ _).symm
  rw [h, toCone_comp_subschemeι]
  exact CategoryTheory.Over.w (toTot e A)

/-- **Pointwise vanishing on the zero section (variable level).** If a morphism `j : S → Tot(A^{⊕(N+1)})` over
`b : S → X` sends `y` into the image of the zero section, then every coordinate of the section of `b^*V`
corresponding to `j` (`totalSpaceHomEquiv`) is zero at `y`. Proof: the tautological coordinates `τ_i` pull back
to `0` along the zero section (`sectionPullbackAlong_zeroSection_tautological`, `sectionPullbackAlong_naturality`),
hence vanish at `zeroSection c = j y` (`isZeroAt_of_sectionPullbackAlong_eq_zero`), hence `j^*τ_i` vanishes at `y`
(`isZeroAt_sectionPullbackAlong_of_isZeroAt`); the coordinate of `j` is `j^*τ_i` up to the transport
isomorphisms (`totalSpaceHomEquiv_coordinate_homMk`), which preserve `IsZeroAt` (`isZeroAt_map`). -/
theorem isZeroAt_coordinate_of_mem_range_zeroSection {Y : AlgebraicGeometry.Scheme.{u}} (A : Y.Modules)
    [A.IsLineBundle] (N : ℕ) {S : AlgebraicGeometry.Scheme.{u}} (b : S ⟶ Y)
    (j : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left)
    (hb : j ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = b)
    (y : S) (hy : j.base y ∈ Set.range
      (AlgebraicGeometry.Scheme.zeroSection (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).base)
    (i : Fin (N + 1)) :
    IsZeroAt ((((AlgebraicGeometry.Scheme.Modules.pullback b).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (CategoryTheory.Over.mk b) (CategoryTheory.Over.homMk j hb))) y := by
  subst hb
  obtain ⟨c, hc⟩ := hy
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let p := T.hom
  let σ := AlgebraicGeometry.Scheme.zeroSection V
  let πi := (AlgebraicGeometry.Scheme.Modules.pullback p).map
    (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)
  let τ := AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (CategoryTheory.CategoryStruct.id T)
  have hnat := sectionPullbackAlong_naturality σ πi τ
  have hz : sectionPullbackAlong σ τ = 0 :=
    AlgebraicGeometry.Scheme.sectionPullbackAlong_zeroSection_tautological V
  have hσ : sectionPullbackAlong σ ((πi.val.app (Opposite.op ⊤)).hom τ) = 0 :=
    hnat.trans ((congrArg (fun z => ((((AlgebraicGeometry.Scheme.Modules.pullback σ).map πi).val.app
      (Opposite.op ⊤)).hom z)) hz).trans (map_zero _))
  have h2 : IsZeroAt ((πi.val.app (Opposite.op ⊤)).hom τ) (j.base y) := by
    rw [← hc]
    exact isZeroAt_of_sectionPullbackAlong_eq_zero σ _ _ c hσ
  have h3 := isZeroAt_sectionPullbackAlong_of_isZeroAt j _ _ y h2
  have h4 : (((AlgebraicGeometry.Scheme.Modules.pullback (j ≫ p)).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (j ≫ p))
        (CategoryTheory.Over.homMk j rfl)) =
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (rfl : j ≫ p = j ≫ p)).hom.app A).val.app
        (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp j p).hom.app A).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong j ((πi.val.app (Opposite.op ⊤)).hom τ))) :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_homMk (fun _ : Fin (N + 1) => A) j (j ≫ p) rfl i
  rw [h4]
  exact isZeroAt_map _ _ y (isZeroAt_map _ _ y h3)

/-- `toCone` avoids the vertex section: its image lies in `Z^× = Z ∖ σ(C)`. Pointwise: if `toCone y = σ(c)` then
`toTot.left y = zeroSection(c)`, so all coordinates `z'_i` of `toTot` vanish at `y`
(`isZeroAt_coordinate_of_mem_range_zeroSection`), contradicting `coord_nowhereZero`. -/
theorem range_toCone_subset :
    Set.range (toCone e E A).base ⊆
      Set.range (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι.base := by
  rw [AlgebraicGeometry.Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  -- the vertex section σ₀ : C → Z (the same term as in the definition of `puncturedCone`)
  let I : (AlgebraicGeometry.Scheme.totalSpace V).left.IdealSheafData :=
    ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (E.F j) (E.homogeneous j))
  let σ0 : C ⟶ (twistedAffineCone A N E.deg E.F E.homogeneous).left :=
    (AlgebraicGeometry.IsClosedImmersion.lift I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) (by
        obtain ⟨τ, hτ'⟩ := zeroSection_mem_twistedAffineCone A N E.deg hdeg E.F E.homogeneous
        rw [← hτ']
        exact AlgebraicGeometry.Scheme.Hom.le_ker_comp _ _) : C ⟶ I.subscheme)
  have hσ0 : σ0 ≫ I.subschemeι = AlgebraicGeometry.Scheme.zeroSection V :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac I.subschemeι (AlgebraicGeometry.Scheme.zeroSection V) _
  show (toCone e E A).base y ∉ Set.range σ0.base
  rintro ⟨c, hc⟩
  have h1 : (toTot e A).left.base y ∈ Set.range (AlgebraicGeometry.Scheme.zeroSection V).base := by
    refine ⟨c, ?_⟩
    rw [← hσ0, ← toCone_comp_subschemeι e E A]
    exact congrArg I.subschemeι.base hc
  obtain ⟨i, hi⟩ := coord_nowhereZero e A y
  apply hi
  have h := isZeroAt_coordinate_of_mem_range_zeroSection A N (base e A) (toTot e A).left
    (CategoryTheory.Over.w (toTot e A)) y h1 i
  have hm : (CategoryTheory.Over.homMk (toTot e A).left (CategoryTheory.Over.w (toTot e A)) :
      CategoryTheory.Over.mk (base e A) ⟶
        AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) = toTot e A :=
    CategoryTheory.Over.OverMorphism.ext rfl
  rw [hm, toTot_coord e A i] at h
  exact h

/-- `β : Tot(L)^× → Z^×`, the lift of `toCone` through the open immersion `Z^× ↪ Z`. -/
def hom : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶
    (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme :=
  AlgebraicGeometry.IsOpenImmersion.lift (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι (toCone e E A)
    (range_toCone_subset e E A hdeg)

theorem hom_comp_ι :
    hom e E A hdeg ≫ (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι = toCone e E A :=
  AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _

/-- First component of `β ≫ g = π`: `β ≫ t = t'`. -/
theorem hom_comp_base :
    hom e E A hdeg ≫ puncturedConeToProduct.base e E A hdeg = base e A := by
  have h : hom e E A hdeg ≫ puncturedConeToProduct.base e E A hdeg =
      (hom e E A hdeg ≫ (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι) ≫
        (twistedAffineCone A N E.deg E.F E.homogeneous).hom :=
    (Category.assoc _ _ _).symm
  rw [h, hom_comp_ι]
  exact toCone_comp_hom e E A

/-- **Transport of coordinates along a morphism of bases (variable level).** Let `m : Over.mk t ⟶ Tot(V)` be a
morphism over `t : T → Y`, `β : S → T`, `b : S → Y` with `β ≫ t = b`, and `m' : Over.mk b ⟶ Tot(V)` with
`β ≫ m.left = m'.left`. Then `β^*` of the `i`-th coordinate of `m`, transported along `pullbackComp β t` and
`pullbackCongr hb`, is the `i`-th coordinate of `m'`. Proof: `subst`, `totalSpaceHomEquiv_naturality_coordinate`
(the coordinate of `Over.homMk β _ ≫ m`), and `Over.OverMorphism.ext` (`Over.homMk β _ ≫ m = m'`). -/
theorem coordinate_pullback_transport {Y : AlgebraicGeometry.Scheme.{u}} (A : Y.Modules) [A.IsLineBundle] (N : ℕ)
    {S T : AlgebraicGeometry.Scheme.{u}} (t : T ⟶ Y) (β : S ⟶ T) (b : S ⟶ Y) (hb : β ≫ t = b)
    (m : CategoryTheory.Over.mk t ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    (m' : CategoryTheory.Over.mk b ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    (hm : β ≫ m.left = m'.left) (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong β
          ((((AlgebraicGeometry.Scheme.Modules.pullback t).map
            (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk t) m)))) =
      (((AlgebraicGeometry.Scheme.Modules.pullback b).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk b) m') := by
  subst hb
  have hn : (((AlgebraicGeometry.Scheme.Modules.pullback (β ≫ t)).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk (β ≫ t))
          ((CategoryTheory.Over.homMk β rfl : CategoryTheory.Over.mk (β ≫ t) ⟶ CategoryTheory.Over.mk t) ≫ m)) =
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong β
          ((((AlgebraicGeometry.Scheme.Modules.pullback t).map
            (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk t) m))) :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate (fun _ : Fin (N + 1) => A)
      (CategoryTheory.Over.mk t) β m i
  have hmm : (CategoryTheory.Over.homMk β rfl : CategoryTheory.Over.mk (β ≫ t) ⟶ CategoryTheory.Over.mk t) ≫ m
      = m' :=
    CategoryTheory.Over.OverMorphism.ext hm
  rw [hmm] at hn
  exact hn.symm

/-- `β ≫ toTot_W.left = toTot.left` (`toTot_W = puncturedConeToProduct.toTot`, i.e. `W ↪ Z ↪ Tot(V)`). -/
theorem hom_comp_toTot_left :
    hom e E A hdeg ≫ (puncturedConeToProduct.toTot e E A hdeg).left = (toTot e A).left := by
  have h1 : hom e E A hdeg ≫ (puncturedConeToProduct.toTot e E A hdeg).left =
      (hom e E A hdeg ≫ (puncturedCone A N E.deg hdeg E.F E.homogeneous).ι) ≫
        (coneIdeal e E A).subschemeι :=
    (Category.assoc _ _ _).symm
  rw [h1, hom_comp_ι]
  exact toCone_comp_subschemeι e E A

/-- `puncturedConeToProduct.coord` unfolded (definitional). -/
theorem puncturedConeToProduct_coord_eq (i : Fin (N + 1)) :
    puncturedConeToProduct.coord e E A hdeg i =
      (((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk (puncturedConeToProduct.base e E A hdeg))
          (puncturedConeToProduct.toTot e E A hdeg)) := rfl

/-- `hom_pullback_coord` with `z_W` written as the coordinate of `toTot_W`: `coordinate_pullback_transport` with
`m = toTot_W`, `m' = toTot` (`hom_comp_toTot_left`), then `toTot_coord`. (Stated separately so that every
`Eq.trans` step is syntactic.) -/
theorem hom_pullback_coord' (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base e E A hdeg)).hom.app A).val.app
        (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg)
          (puncturedConeToProduct.base e E A hdeg)).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (hom e E A hdeg)
          ((((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).map
            (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom
            (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
              (CategoryTheory.Over.mk (puncturedConeToProduct.base e E A hdeg))
              (puncturedConeToProduct.toTot e E A hdeg))))) = coord e A i :=
  (coordinate_pullback_transport A N (puncturedConeToProduct.base e E A hdeg) (hom e E A hdeg) (base e A)
    (hom_comp_base e E A hdeg) (puncturedConeToProduct.toTot e E A hdeg) (toTot e A)
    (hom_comp_toTot_left e E A hdeg) i).trans (toTot_coord e A i)

/-- `β^*(z_W)_i`, transported along `pullbackComp β t` and `pullbackCongr (β ≫ t = t')`, is `z'_i`
(`z_W = puncturedConeToProduct.coord`). -/
theorem hom_pullback_coord (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base e E A hdeg)).hom.app A).val.app
        (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg)
          (puncturedConeToProduct.base e E A hdeg)).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i))) = coord e A i :=
  (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base e E A hdeg)).hom.app A).val.app
        (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg)
          (puncturedConeToProduct.base e E A hdeg)).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (hom e E A hdeg) z))) (puncturedConeToProduct_coord_eq e E A hdeg i)).trans
    (hom_pullback_coord' e E A hdeg i)

/-- `β ≫ t = π ≫ pr₁` (`hom_comp_base` with `base e A` unfolded; kept as a separate theorem so that the two
spellings of the base meet only here — see the docstring of `hom_isTotalSpaceToConeHom`). -/
theorem hom_comp_base' :
    hom e E A hdeg ≫ puncturedConeToProduct.base e E A hdeg = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ≫ (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :=
  hom_comp_base e E A hdeg

/-- Transport along the identity `base e A = π ≫ pr₁` (definitional: the proof is `rfl`, so `pullbackCongr rfl`
reduces to the identity). -/
theorem pullbackCongr_base_coord (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (rfl : base e A = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ≫ (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))).hom.app A).val.app (Opposite.op ⊤)).hom
      (coord e A i) = (((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app A).val.app (Opposite.op ⊤)).hom (coordZ e A i) := rfl

/-- `hom_pullback_coord` with the base spelled `π ≫ pr₁`: `β^*(z_W)_i`, transported along `pullbackComp β t` and
`pullbackCongr (β ≫ t = π ≫ pr₁)`, is `(pullbackComp π pr₁)(z_i)`. This is the form of the hypothesis `hx` of
`Modules.coordinate_transport_of`. Proof: `pullbackCongr_hom_app_val_app_congr` splits the transport into
`pullbackCongr hom_comp_base` (then `hom_pullback_coord`) followed by `pullbackCongr rfl` (`pullbackCongr_base_coord`);
every junction is syntactic (a defeq comparison of two `pullbackCongr`s with different proofs costs > 45 s). -/
theorem hom_pullback_coordZ (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base' e E A hdeg)).hom.app A).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg) (puncturedConeToProduct.base e E A hdeg)).hom.app A).val.app
      (Opposite.op ⊤)).hom (sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i))) = (((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app A).val.app (Opposite.op ⊤)).hom (coordZ e A i) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_val_app_congr (hom_comp_base e E A hdeg)
    (hom_comp_base' e E A hdeg) (rfl : base e A = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ≫ (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) A ((((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg) (puncturedConeToProduct.base e E A hdeg)).hom.app A).val.app
      (Opposite.op ⊤)).hom (sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i)))).trans
    ((congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (rfl : base e A = (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) ≫ (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))).hom.app A).val.app (Opposite.op ⊤)).hom
      z) (hom_pullback_coord e E A hdeg i)).trans (pullbackCongr_base_coord e A i))

/-- The pulled-back coordinates `β^*(z_W)_i`, `i = 0, …, N`, as one function. Kept as a named, η-reduced function on
purpose: the tuple variable of `projectivizationMorphism_congr_iso` / `exists_not_isZeroAt_iso` is instantiated by
`pullCoord e E A hdeg`, so that the instantiated statements contain `pullCoord e E A hdeg ℓ` and never the β-redex
`(fun ℓ => β^*(z_W)_ℓ) ℓ`; a redex against its reduct under a `DFunLike.coe` head makes the kernel unfold
`pullbackComp` down to linear maps (measured 19 s of type checking). -/
def pullCoord : Fin (N + 1) →
    (((AlgebraicGeometry.Scheme.Modules.pullback (hom e E A hdeg)).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)).val.obj
      (Opposite.op ⊤) : Type u) :=
  fun i => sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i)

theorem pullCoord_apply (i : Fin (N + 1)) :
    pullCoord e E A hdeg i = sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i) := rfl

/-- **Transport of the coordinates of `toTot_W` along `β`, as an isomorphism `Θ : β^*t^*A ≅ t'^*A`.**
`Θ := (pullbackComp β t).app A ≪≫ (pullbackCongr hom_comp_base).app A` sends `β^*(z_W)_i` to `z'_i`
(`hom_pullback_coord`, restated with `Modules.Hom.app` as `projectivizationMorphism_congr_iso` needs it; every step is
a syntactic rewrite with a variable-level spelling lemma). -/
theorem theta_transport_hom_app (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg) (puncturedConeToProduct.base e E A hdeg)).app A ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base e E A hdeg)).app A).hom.app ⊤)
      (pullCoord e E A hdeg i) = coord e A i := by
  rw [pullCoord_apply, AlgebraicGeometry.Scheme.Modules.Hom.app_top_apply,
    AlgebraicGeometry.Scheme.Modules.Iso.trans_hom_val_app_apply',
    AlgebraicGeometry.Scheme.Modules.natIso_app_hom_val_app_apply,
    AlgebraicGeometry.Scheme.Modules.natIso_app_hom_val_app_apply]
  exact hom_pullback_coord e E A hdeg i

/-- The pulled-back coordinates `β^*(z_W)_i` are nowhere all zero on `Tot(L)^×`: they are carried by the isomorphism
`Θ` to `z'_i` (`hom_pullback_coord`), which are nowhere all zero (`coord_nowhereZero`); `IsZeroAt` is invariant
under isomorphisms (`isZeroAt_natIso_app_iff`, twice). -/
theorem exists_not_isZeroAt_sectionPullbackAlong_hom_coord
    (y : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme) :
    ∃ i, ¬ IsZeroAt (sectionPullbackAlong (hom e E A hdeg) (puncturedConeToProduct.coord e E A hdeg i)) y := by
  obtain ⟨i, hi⟩ := coord_nowhereZero e A y
  refine ⟨i, fun hz => hi ?_⟩
  rw [← hom_pullback_coord e E A hdeg i]
  exact (AlgebraicGeometry.Scheme.Modules.isZeroAt_natIso_app_iff _ _ _ y).mpr
    ((AlgebraicGeometry.Scheme.Modules.isZeroAt_natIso_app_iff _ _ _ y).mpr hz)

/-- `exists_not_isZeroAt_sectionPullbackAlong_hom_coord` for the function `pullCoord`. -/
theorem exists_not_isZeroAt_pullCoord
    (y : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme) :
    ∃ i, ¬ IsZeroAt (pullCoord e E A hdeg i) y := by
  obtain ⟨i, hi⟩ := exists_not_isZeroAt_sectionPullbackAlong_hom_coord e E A hdeg y
  exact ⟨i, by rw [pullCoord_apply]; exact hi⟩

/-- `β` is a `k`-morphism for the `k`-structures `overK` on `Tot(L)^×` and `puncturedConeToProduct.overK` on `Z^×`
(both are "base point, then `C ↘ Spec k`", and `β ≫ t = t'` is `hom_comp_base`). -/
theorem hom_isOver :
    letI := overK e A
    letI := puncturedConeToProduct.overK e E A hdeg
    (hom e E A hdeg).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  letI := overK e A
  letI := puncturedConeToProduct.overK e E A hdeg
  refine ⟨?_⟩
  change hom e E A hdeg ≫ (puncturedConeToProduct.base e E A hdeg ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
    base e A ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  rw [← Category.assoc, hom_comp_base]

/-- Second component of `β ≫ g = π`: `β ≫ Φ = x'` (`Φ = puncturedConeToProduct.toX`).

Source: eq. (2.1) of the paper; Stacks 01NE (`projectiveSpace_hom_ext_of_sections`).

Proof. `e.emb` is a monomorphism (closed immersion), so it suffices to show
`β ≫ Φ ≫ e.emb = x' ≫ e.emb` (`cancel_mono`). Write `W := Z^×`, `t := puncturedConeToProduct.base`,
`z_W := puncturedConeToProduct.coord`, `φ_W := projectivizationMorphism (t^*A) z_W`.
1. `Φ ≫ e.emb = φ_W` (`IsClosedImmersion.lift_fac`, definition of `toX`).
2. `β` is a `k`-morphism (`hom_isOver`), so `β ≫ φ_W = projectivizationMorphism (β^*t^*A) (β^*z_W)`
   (`projectivizationMorphism_pullback`; the pulled-back tuple is nowhere all zero by
   `exists_not_isZeroAt_sectionPullbackAlong_hom_coord`).
3. `Θ : β^*t^*A ≅ t'^*A` sends `β^*(z_W)_i` to `z'_i` (`theta_transport_hom_app`), so
   `projectivizationMorphism_congr_iso Θ` and `projectivizationMorphism_congr_tuple` (module
   `S3PositiveLine.MorphismNearZeroSectionCompat`) give
   `projectivizationMorphism (β^*t^*A) (β^*z_W) = projectivizationMorphism (t'^*A) z'`.
4. `projectivizationMorphism (t'^*A) z' = x' ≫ e.emb` (`projectivizationMorphism_coord_eq`, module `…BackwardCoord`). -/
theorem hom_comp_toX :
    hom e E A hdeg ≫ puncturedConeToProduct.toX e E A hdeg = toX e A := by
  letI := overK e A
  letI := puncturedConeToProduct.overK e E A hdeg
  haveI := hom_isOver e E A hdeg
  -- the source of `Θ` is spelled `(pullback t ⋙ pullback β).obj A`; give it its line-bundle instance by hand
  haveI : ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg) ⋙
      AlgebraicGeometry.Scheme.Modules.pullback (hom e E A hdeg)).obj A).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback (hom e E A hdeg)
      ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
  have hfac : puncturedConeToProduct.toX e E A hdeg ≫ e.emb =
      projectivizationMorphism (k := k)
        ((AlgebraicGeometry.Scheme.Modules.pullback (puncturedConeToProduct.base e E A hdeg)).obj A)
        (puncturedConeToProduct.coord e E A hdeg) (puncturedConeToProduct.coord_nowhereZero e E A hdeg) :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have hR : projectivizationMorphism (k := k) ((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A)
      (coord e A) (coord_nowhereZero e A) = toX e A ≫ e.emb := projectivizationMorphism_coord_eq e A
  rw [← cancel_mono e.emb, Category.assoc, hfac, ← hR]
  -- `rw` cannot be used for the next two steps: `(pullback t ⋙ pullback β).obj A` and
  -- `(pullback β).obj ((pullback t).obj A)` are definitionally but not syntactically equal, so the junctions are
  -- made by `Eq.trans` (a defeq check on the *arguments* of `projectivizationMorphism`, at the level of objects).
  exact (projectivizationMorphism_pullback (hom e E A hdeg) _ (puncturedConeToProduct.coord e E A hdeg)
      (puncturedConeToProduct.coord_nowhereZero e E A hdeg)
      (exists_not_isZeroAt_sectionPullbackAlong_hom_coord e E A hdeg)).trans
    ((projectivizationMorphism_congr_iso _ _ ((AlgebraicGeometry.Scheme.Modules.pullbackComp (hom e E A hdeg) (puncturedConeToProduct.base e E A hdeg)).app A ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr (hom_comp_base e E A hdeg)).app A)
      (pullCoord e E A hdeg) (exists_not_isZeroAt_pullCoord e E A hdeg)
      (exists_not_isZeroAt_iso _ _ (exists_not_isZeroAt_pullCoord e E A hdeg))).trans
    (projectivizationMorphism_congr_tuple _ (funext (theta_transport_hom_app e E A hdeg)) _ _))

/-- `β ≫ g = π`, where `g = puncturedConeToProduct = pullback.lift t Φ`. -/
theorem hom_comp_puncturedConeToProduct :
    hom e E A hdeg ≫ puncturedConeToProduct e E A hdeg =
      AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A) := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [Category.assoc]
    unfold puncturedConeToProduct
    rw [CategoryTheory.Limits.pullback.lift_fst]
    exact hom_comp_base e E A hdeg
  · rw [Category.assoc]
    unfold puncturedConeToProduct
    rw [CategoryTheory.Limits.pullback.lift_snd]
    exact hom_comp_toX e E A hdeg

/-- `β = hom` satisfies the backward characterization `IsTotalSpaceToConeHom e E A hdeg β`.

Its first component `β ≫ g = π` is `hom_comp_puncturedConeToProduct`. The coordinate identity is
`Modules.coordinate_transport_two` (module `…BackwardTransportTwo`) instantiated with
`hπ := hom_comp_base'`, `x := puncturedConeToProduct.coord i`, `hy := rfl` after unfolding
`puncturedConeToProduct.coordOverProduct` (`delta`), `hx := hom_pullback_coordZ i`, and `rfl`/`HEq.rfl` for the
equations between the two spellings of `Tot(L)^×`, `C ×_k X`, `β`, `π`, `pr₁` and `z_i`.

Source: eq. (2.1) of the paper ("`β^*z_i = z_i`" is how `β` is defined). Self-contained transport computation.

**Why this shape.** The body of `def IsTotalSpaceToConeHom`
carries abstracted instance proofs (`conePuncturedLineBundle.eval._proof_1`, `IsConeToTotalSpaceHom._proof_3/_4`),
every fact proved here carries the inline instances; comparing the two spellings under a `DFunLike.coe` head costs
> 60 s (a single such `rfl` times out), because both the elaborator and the kernel unfold `Modules.pullback`/
`pullbackComp` down to linear maps before they reach the proof-irrelevant argument. `coordinate_transport_two` keeps
the two spellings in separate variables and relates them only at the level of schemes and morphisms; its implicit
arguments come first so that the conclusion is unified with the goal (goal spelling) before any fact (fact spelling)
is looked at. The witness `hβ` is left as the hole `?w` while the coordinate goal is solved, so that the goal's own
(`_proof`-spelled) binder type, not the type of `hom_comp_puncturedConeToProduct`, drives the unification. Measured:
elaboration + kernel < 2 s. -/
theorem hom_isTotalSpaceToConeHom : IsTotalSpaceToConeHom e E A hdeg (hom e E A hdeg) := by
  refine ⟨?w, fun i => ?coord⟩
  case coord =>
    exact AlgebraicGeometry.Scheme.Modules.coordinate_transport_two (hom_comp_base' e E A hdeg)
      (puncturedConeToProduct.coord e E A hdeg i) (by delta puncturedConeToProduct.coordOverProduct; rfl)
      (hom_pullback_coordZ e E A hdeg i) rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  case w => exact hom_comp_puncturedConeToProduct e E A hdeg

end puncturedTotalSpaceToCone

/-- There is a `β : Tot(L)^× → Z^×` satisfying the backward characterization.

Source: eq. (2.1) of the paper; Stacks 02OR (pullback of the zero scheme), 01NE
(uniqueness of morphisms to `ℙ^N`), 03GL (the vanishing ideal).

Assembled from the skeleton in namespace `puncturedTotalSpaceToCone` (see the module docstring):
`β := hom`, `β ≫ g = π` is `hom_comp_puncturedConeToProduct`, the coordinate identity is
`hom_isTotalSpaceToConeHom`. -/
theorem puncturedTotalSpace_exists_isTotalSpaceToConeHom {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) :
    ∃ β : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶ (puncturedCone A N E.deg hdeg E.F E.homogeneous).toScheme,
      IsTotalSpaceToConeHom e E A hdeg β :=
  ⟨puncturedTotalSpaceToCone.hom e E A hdeg, puncturedTotalSpaceToCone.hom_isTotalSpaceToConeHom e E A hdeg⟩

end
