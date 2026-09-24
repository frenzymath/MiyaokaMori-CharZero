import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationScalar
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationChart
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr

/-! # The canonical evaluation map of a relative Proj

The canonical evaluation map `π^*S_m → O(m)` on the relative Proj `π : Proj_X S → X` of a graded
quasi-coherent algebra `S` (evaluation of the degree-`m` coordinate functions), and the notion
"`φ : g^*S_m → M` is induced by `τ : T → Proj_X S`": `g = τ ≫ π`, and `φ` factors through
`g^*S_m ≅ τ^*π^*S_m` as `τ^*(evaluation)` followed by a map `τ^*O(m) → M`. The quotient
`ρ^*(S_k)_m → L^{-m}` obtained by evaluating the weight-`m` functions on an affine jet in
Proposition 3.2 of the paper is such an induced map.

Source: Stacks 01MN, 01NR, 01O4; Proposition 3.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A section of the `m`-th graded piece, placed in the degree-`m` homogeneous part of the sections
ring `A(U) = ⊕_m Γ(U, S_m)` (`DirectSum.of` restricted to its range, i.e. `sectionsGrading U m`). -/
noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.sectionsOf {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.Opens) (m : ℕ) :
    Γ(S.part m, U) →+ S.sectionsGrading U m :=
  (DirectSum.of (S.sectionsPiece U) m).rangeRestrict

/-! ## The building blocks of `relativeProj.evaluation`

The local evaluation map on an affine open, its additivity, its naturality on the basis of affine
opens, and its `O_X`-linearity; the evaluation map itself is assembled from them at the end of the
file. -/

/-- The evaluation map on sections over an affine open `V`, `Γ(S_m, V) → Γ(O(m), π⁻¹V)`:
`Γ(S_m, V) → A(V)_m` (`sectionsOf`) `→ Γ(Proj A(V), O(m))` (`Proj.twistSection`, `a ↦ a/1`, Stacks 01MN)
`→ Γ(π⁻¹V, φ_V^*O(m))` (pullback along `φ_V : π⁻¹V ≅ Proj A(V)`, adjunction unit)
`→ Γ(π⁻¹V, O(m))` (`twistAffineIso`, Stacks 01NR). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.evaluationLocal
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens)
    (x : Γ(S.part m, V.1)) :
    Γ(AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ),
      (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) :=
  let φ := (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom
  let ι := ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι
  let G := AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ)
  let a := S.sectionsOf V.1 m x
  let s : Γ(G, ⊤) := AlgebraicGeometry.Proj.twistSection (S.sectionsGrading V.1) a.1 a.2
  let t : Γ((AlgebraicGeometry.Scheme.Modules.pullback φ).obj G, φ ⁻¹ᵁ ⊤) :=
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app G).app ⊤).hom s
  let t' : Γ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).restrict ι, φ ⁻¹ᵁ ⊤) :=
    ((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V (m : ℤ)).inv.app (φ ⁻¹ᵁ ⊤)).hom t
  -- Γ(T|_{π⁻¹V}, W) = Γ(T, ι ''ᵁ W) (Mathlib `restrict_obj`), and ι ''ᵁ (φ⁻¹ᵁ ⊤) = ι ''ᵁ ⊤ ≥ π⁻¹V
  ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map (CategoryTheory.homOfLE (by
    rw [AlgebraicGeometry.Scheme.Hom.preimage_top, AlgebraicGeometry.Scheme.Opens.ι_image_top]) :
      (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ⟶ ι ''ᵁ (φ ⁻¹ᵁ ⊤)).op).hom t'

/-- The inclusion used in the last step of `evaluationLocal`: `π⁻¹V ≤ ι ''ᵁ (φ⁻¹ᵁ ⊤)` (as `ι ''ᵁ ⊤ = π⁻¹V`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (V : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 ≤
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ
        ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) := by
  rw [AlgebraicGeometry.Scheme.Hom.preimage_top, AlgebraicGeometry.Scheme.Opens.ι_image_top]

/-- `evaluationLocal` written without `let`s (a definitional equality, used as a bridge lemma: proofs
only `rw` with it and never `simp`/`unfold` the definition body, which would expand `Γ(-, -)` and `.hom`
into shapes that are no longer well-typed at implicit transparency). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens)
    (x : Γ(S.part m, V.1)) :
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x =
      ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map
          (CategoryTheory.homOfLE
            (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V)).op).hom
        (((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V (m : ℤ)).inv.app
            ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
                (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app
                (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ))).app ⊤).hom
            (AlgebraicGeometry.Proj.twistSection (S.sectionsGrading V.1)
              (S.sectionsOf V.1 m x).1 (S.sectionsOf V.1 m x).2))) := rfl

/-! ## Additivity of `Proj.twistSection`

Stacks 01MN: `a ↦ a/1` is additive pointwise; every value of `homogeneousSection` is
`Localization.mk a 1`, so `(a + b)/1 = a/1 + b/1` and `0/1 = 0`. The statements carry an explicit
equation `e` so that they can be used with `rw` in the presence of the dependent proof `hh : h ∈ 𝒜 d`. -/

/-- `twistSection` is additive: if `h = f + g` then `twistSection h = twistSection f + twistSection g`. -/
theorem AlgebraicGeometry.Proj.twistSection_add {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f g h : A}
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 d) (hh : h ∈ 𝒜 d) (e : h = f + g) :
    (AlgebraicGeometry.Proj.twistSection 𝒜 h hh : Γ(AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ), ⊤)) =
      AlgebraicGeometry.Proj.twistSection 𝒜 f hf + AlgebraicGeometry.Proj.twistSection 𝒜 g hg := by
  subst e
  exact Subtype.ext (funext fun _ => (Localization.add_mk_self _ _ _).symm)

/-- `twistSection` preserves zero: if `f = 0` then `twistSection f = 0`. -/
theorem AlgebraicGeometry.Proj.twistSection_zero {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) {d : ℕ} [GradedRing 𝒜] {f : A}
    (hf : f ∈ 𝒜 d) (e : f = 0) :
    (AlgebraicGeometry.Proj.twistSection 𝒜 f hf : Γ(AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ), ⊤)) = 0 := by
  subst e
  exact Subtype.ext (funext fun _ => Localization.mk_zero _)

/-- `twistSection` is linear over degree-zero elements (Stacks 01MN: `A_d → Γ(Proj A, O(d))` is
`A_0`-linear): if `ũ ∈ Γ(Proj 𝒜, ⊤)` is pointwise the fraction `u/1` (`u ∈ 𝒜 0`) and `h = u * f`, then
`twistSection h = ũ • twistSection f`. Pointwise, `(u * f)/1 = (u/1) · (f/1)` (`Localization.mk_mul`), and
the module structure of `sectionsSubmodule` (`Module.compHom _ (sectionCoefficientMap 𝒜 U)`) is exactly
pointwise multiplication. -/
theorem AlgebraicGeometry.Proj.twistSection_smul {σ A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {u f h : A}
    (hf : f ∈ 𝒜 d) (hh : h ∈ 𝒜 d) (e : h = u * f) (ũ : Γ(AlgebraicGeometry.Proj 𝒜, ⊤))
    (hũ : ∀ x : (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens),
      HomogeneousLocalization.val (ũ.1 x) = Localization.mk u 1) :
    (AlgebraicGeometry.Proj.twistSection 𝒜 h hh : Γ(AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ), ⊤)) =
      @HSMul.hSMul Γ(AlgebraicGeometry.Proj 𝒜, ⊤) Γ(AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ), ⊤)
        Γ(AlgebraicGeometry.Proj.twist 𝒜 (d : ℤ), ⊤) instHSMul ũ
        (AlgebraicGeometry.Proj.twistSection 𝒜 f hf) := by
  subst e
  refine Subtype.ext (funext fun x => ?_)
  change Localization.mk (u * f) 1 = HomogeneousLocalization.val (ũ.1 x) * Localization.mk f 1
  rw [hũ x, Localization.mk_mul, one_mul]

/-- `evaluationLocal` preserves zero.

Source: Stacks 01MN (additivity of `Proj.twistSection`), 01NR (`twistAffineIso`).

Proof: `evaluationLocal` is a composite of five maps (`evaluationLocal_eq`); `sectionsOf V.1 m`
(the `rangeRestrict` of `DirectSum.of`), the section maps of the adjunction unit `unit.app G` and of
the inverse of `twistAffineIso`, and `T.presheaf.map _` are additive group homomorphisms (`map_zero`);
the only nontrivial step, `Proj.twistSection`, is handled by `twistSection_zero` (pointwise `0/1 = 0`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_map_zero
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens) :
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V 0 = 0 := by
  have e : ((S.sectionsOf V.1 m 0 : S.sectionsGrading V.1 m) : S.sectionsRing V.1) = 0 := by
    rw [map_zero]; rfl
  rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Proj.twistSection_zero (S.sectionsGrading V.1) _ e]
  erw [map_zero, map_zero, map_zero]

/-- `evaluationLocal` is additive. Same source and route as `evaluationLocal_map_zero` (the key step is
the additivity `twistSection_add` of `Proj.twistSection`, Stacks 01MN). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_map_add
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens)
    (x y : Γ(S.part m, V.1)) :
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V (x + y) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x +
        AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V y := by
  have e : ((S.sectionsOf V.1 m (x + y) : S.sectionsGrading V.1 m) : S.sectionsRing V.1) =
      (S.sectionsOf V.1 m x : S.sectionsRing V.1) + (S.sectionsOf V.1 m y : S.sectionsRing V.1) := by
    rw [map_add]; rfl
  rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Proj.twistSection_add (S.sectionsGrading V.1)
      (S.sectionsOf V.1 m x).2 (S.sectionsOf V.1 m y).2 _ e]
  erw [map_add, map_add, map_add]

/-- `evaluationLocal` packaged as an additive group homomorphism on the basis of affine opens. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.evaluationBaseApp
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ)
    (V : (CategoryTheory.InducedCategory X.Opens (fun V : X.affineOpens => V.1))ᵒᵖ) :
    ((CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙
        (S.part m).presheaf).obj V ⟶
      ((CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf).obj V :=
  AddCommGrpCat.ofHom
    { toFun := AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V.unop
      map_zero' := AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_map_zero S m V.unop
      map_add' := AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_map_add S m V.unop }


/-! ## Ingredients of `evaluationBase_naturality`

Both sides are sections of `Γ(O(m), π⁻¹W)`. Cover `π⁻¹W` by the images `π⁻¹W′` of the charts `W′`, where
`W′ = D_V(f) ⊆ W` is simultaneously a principal open of `V` and of `W`; on each piece the limit projection
`twistπ m W′` is injective on the image of the chart `W′` (Stacks 01LI, `isIso_restrictFunctor_map_twistπ`).
The value of `twistπ m W′` on `evaluationLocal` is computed from `twistπ_transition`
(`twistπ W′ = twistπ V ≫ θ`), from `twistπ_app_twistAffineIso_inv_unit` (`twistπ V` sends the core of
`evaluationLocal` back to `a/1`; via the general lemma of `RelativeProjEvaluationChart`, so `twistAffineIso.inv`
need not be unfolded) and from the pointwise formula for `θ` (`a/1 ↦ (res a)/1`); both sides are `(res a)/1`.

**Spelling discipline.** This section involves two spellings of the same objects: `relativeProj.twist S m` /
`Proj.twist (S.sectionsGrading V.1) m` / `relativeProj.twistπ S m V` (used in this file and by `twistAffineIso`)
and `S.toGradedAffineAlgebra.twist m` / `Proj.twist (S.grading ⟨V.1, V.2⟩) m` / `GradedAffineAlgebra.twistπ`
(used by `twistChartHom` and `twistπ_transition`). The two spellings are bridged only at the **top level** by
`rfl` / `HEq.rfl` (the bridge arguments of `comp_eq_of_heq_bridge` and `app_image_eq_of_chartHomShape_heq`);
the kernel must never compare them under `Functor.map` / `≫` / `Iso.hom` (measured at 40–50 s per occurrence).
Charts are always written `S.toGradedAffineAlgebra.projChart ⟨V.1, V.2⟩` (the spelling in the body of
`twistAffineHom`), never `chart S V`. -/

/-! ## A general lemma: the inverse of a chart comparison **isomorphism** applied to the adjunction unit

`twistπ_app_twistAffineIso_inv_unit` is an instance of `RelativeProjEvaluationChart.app_image_eq_of_chartHomShape_heq`;
the wrapper lemma below replaces the hypothesis "`I.hom` is the chart comparison composite" by a **heterogeneous
equality** `HEq I.hom H`, and duplicates every variable of the composite into a "body side" and a "goal side"
copy, bridged by top-level `rfl`/`HEq.rfl`. The reason is kernel time; see its docstring. -/

namespace AlgebraicGeometry.Scheme.Modules

/-- **Sections of the limit projection on the chart, from the chart comparison isomorphism** (variant of
`app_image_eq_of_chartHomShape_heq` for an iso `I : T|_ι ≅ φ^*G`): if `I.hom` is (heterogeneously) the chart
comparison composite `RFIP ≫ pullbackCongr ≫ pullbackComp ≫ φ^*θ` written in a *second* set of variables
(`Qb Pb Yb φb cb ιb hιb Bb Tb Gb θ`, the "body side"), then `k (I.inv (unit s)) = s|_{c⁻¹(ι''(φ⁻¹U))}`.

**Why two copies of every variable (kernel cost).** In the concrete use
(`twistπ_app_twistAffineIso_inv_unit`) the goal-side variables `Q P Y φ c ι hιOI T G k I s` are unified from the
goal (the locked statement: `pushforward c` with the spelling `Proj (S.grading ⟨V.1, V.2⟩) ⟶ S.toGradedAffineAlgebra.
relativeProj.left`, the literal proof `V.2`, the synthesized `IsOpenImmersion` instance), while the composite must
be *syntactically* the zeta-reduced body of `twistAffineHom` (spelling `(relativeProj S).left`, auxiliary proof
constants `twistAffineHom._proof_n`). Any difference between the two under an applied projection
(`NatTrans.app`, `Iso.hom`, `Hom.app`, `ConcreteCategory.hom` — all `abbrev`-hinted, so the kernel never compares
their arguments lazily) makes the kernel `whnf` the whole `restrictFunctorIsoPullback`/adjunction machinery
(measured 38–45 s). So the body side is unified from `I.hom` through `hIH := HEq.rfl` (`hH := rfl` only names the
composite), and the two sides are bridged by top-level `rfl`/`HEq.rfl` (cheap: no applied projection above them). -/
theorem app_image_eq_of_iso_hom_heq_chartHomShape {Q P Y : AlgebraicGeometry.Scheme.{u}} {φ : Q ⟶ P} {c : P ⟶ Y}
    {ι : Q ⟶ Y} [hφOI : AlgebraicGeometry.IsOpenImmersion φ] [hcOI : AlgebraicGeometry.IsOpenImmersion c]
    {hιOI : AlgebraicGeometry.IsOpenImmersion ι} (hc : φ ≫ c = ι)
    {T : Y.Modules} {G : P.Modules} {U : P.Opens} (s : Γ(G, U))
    (I : @AlgebraicGeometry.Scheme.Modules.restrict _ _ T ι hιOI ≅ (pullback φ).obj G)
    (k : T ⟶ (pushforward c).obj G)
    -- body side
    {Qb Pb Yb : AlgebraicGeometry.Scheme.{u}} {φb : Qb ⟶ Pb} {cb : Pb ⟶ Yb} {ιb : Qb ⟶ Yb}
    {hιb : AlgebraicGeometry.IsOpenImmersion ιb} {Bb : pullback ιb ≅ pullback (φb ≫ cb)}
    {Tb : Yb.Modules} {Gb : Pb.Modules} {θ : (pullback cb).obj Tb ⟶ Gb}
    {H : @AlgebraicGeometry.Scheme.Modules.restrict _ _ Tb ιb hιb ⟶ (pullback φb).obj Gb}
    (hH : H = (@restrictFunctorIsoPullback _ _ ιb hιb).hom.app Tb ≫ Bb.hom.app Tb ≫
        (pullbackComp φb cb).inv.app Tb ≫ (pullback φb).map θ)
    (hIH : HEq I.hom H)
    (hQ : Qb = Q) (hP : Pb = P) (hY : Yb = Y) (hφ : HEq φb φ) (hcb : HEq cb c) (hι : HEq ιb ι)
    (hT : HEq Tb T) (hG : HEq Gb G) (hB : HEq Bb (pullbackCongr hc.symm))
    -- θ side
    {P' Y' : AlgebraicGeometry.Scheme.{u}} {c' : P' ⟶ Y'} {T' : Y'.Modules} {G' : P'.Modules}
    {k' : T' ⟶ (pushforward c').obj G'}
    (hθ : HEq θ (((pullbackPushforwardAdjunction c').homEquiv T' G').symm k'))
    (hP' : P' = P) (hY' : Y' = Y) (hc' : HEq c' c) (hT' : HEq T' T) (hG' : HEq G' G) (hk : HEq k' k) :
    k.app (@AlgebraicGeometry.Scheme.Hom.opensFunctor _ _ ι hιOI |>.obj (φ ⁻¹ᵁ U))
        ((I.inv.app (φ ⁻¹ᵁ U)).hom ((((pullbackPushforwardAdjunction φ).unit.app G).app U).hom s)) =
      (show Γ((pushforward c).obj G, @AlgebraicGeometry.Scheme.Hom.opensFunctor _ _ ι hιOI |>.obj (φ ⁻¹ᵁ U)) from
        G.presheaf.map (homOfLE (@preimage_image_preimage_le _ _ _ φ c hφOI hcOI ι hιOI hc U)).op s) := by
  obtain rfl := hQ.symm
  obtain rfl := hP.symm
  obtain rfl := hY.symm
  obtain rfl := (eq_of_heq hφ).symm
  obtain rfl := (eq_of_heq hcb).symm
  obtain rfl := (eq_of_heq hι).symm
  obtain rfl := (eq_of_heq hT).symm
  obtain rfl := (eq_of_heq hG).symm
  obtain rfl : hιOI = hιb := Subsingleton.elim _ _
  obtain rfl := (eq_of_heq hB).symm
  have hI : I.hom = (@restrictFunctorIsoPullback _ _ ι hιOI).hom.app T ≫ (pullbackCongr hc.symm).hom.app T ≫
      (pullbackComp φ c).inv.app T ≫ (pullback φ).map θ := (eq_of_heq hIH).trans hH
  have h0 : I.inv.app (φ ⁻¹ᵁ U) ≫ I.hom.app (φ ⁻¹ᵁ U) = 𝟙 _ := by
    rw [← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]
  have hz : (((@restrictFunctorIsoPullback _ _ ι hιOI).hom.app T ≫ (pullbackCongr hc.symm).hom.app T ≫
      (pullbackComp φ c).inv.app T ≫ (pullback φ).map θ).app (φ ⁻¹ᵁ U))
        ((I.inv.app (φ ⁻¹ᵁ U)).hom ((((pullbackPushforwardAdjunction φ).unit.app G).app U).hom s)) =
      ((pullbackPushforwardAdjunction φ).unit.app G).app U s := by
    rw [← hI]
    exact ConcreteCategory.congr_hom h0 _
  exact app_image_eq_of_chartHomShape_heq hc rfl hz k hθ hP' hY' hc' hT' hG' hk

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `twistAffineIso.hom` is `twistAffineHom` (`asIso_hom`; a definitional equality). -/
theorem twistAffineIso_hom (V : X.affineOpens) (n : ℤ) :
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V n).hom =
      AlgebraicGeometry.Scheme.relativeProj.twistAffineHom S V n := rfl

/-- `φ ≫ c = ι`, with `c` spelled as in the body of `twistAffineHom` (`projChart ⟨V.1, V.2⟩`, the target of
the composite written explicitly as `(relativeProj S).left`). The proof follows the `hc` inside `twistAffineHom`
(`affineIso_inv_ι`) and does not go through `chart S V`. -/
theorem affineIso_hom_comp_projChart (V : X.affineOpens) :
    @CategoryTheory.CategoryStruct.comp AlgebraicGeometry.Scheme.{u} _ _ _
        (AlgebraicGeometry.Scheme.relativeProj S).left
        (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom (S.toGradedAffineAlgebra.projChart ⟨V.1, V.2⟩) =
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι :=
  (congrArg (fun g => (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ≫ g)
    (AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S V)).symm.trans
    (CategoryTheory.Iso.hom_inv_id_assoc (AlgebraicGeometry.Scheme.relativeProj.affineIso S V)
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι)

/-- The pushforward `(ι_{W′})_* O_{W′}(m)` of `O(m)` on the chart `W′`, as a module on `(relativeProj S).left`
(the target scheme of the pushforward is written explicitly as `(relativeProj S).left`, the spelling used in
the rest of this file). -/
def chartPush (m : ℤ) (W' : X.AffineZariskiSite) : (AlgebraicGeometry.Scheme.relativeProj S).left.Modules :=
  (@AlgebraicGeometry.Scheme.Modules.pushforward _ (AlgebraicGeometry.Scheme.relativeProj S).left
    (S.toGradedAffineAlgebra.projChart W')).obj (AlgebraicGeometry.Proj.twist (S.toGradedAffineAlgebra.grading W') m)

/-- `GradedAffineAlgebra.twistπ m W′`, with source spelled `relativeProj.twist S m` and target spelled `chartPush`
(definitionally equal), so that all section computations in `Γ(O(m), Ω)` below use a single spelling. -/
def twistπSite (m : ℤ) (W' : X.AffineZariskiSite) :
    AlgebraicGeometry.Scheme.relativeProj.twist S m ⟶ chartPush S m W' :=
  S.toGradedAffineAlgebra.twistπ m W'

/-- `twistπ` is compatible with the transition maps: `GradedAffineAlgebra.twistπ_transition` transported to the
present spelling by `comp_eq_of_heq_bridge` (top-level `HEq.rfl`). -/
theorem twistπ_comp_twistTransition (m : ℤ) (V : X.affineOpens) {W' : X.AffineZariskiSite}
    (h : W' ≤ AlgebraicGeometry.Scheme.affineSite V) :
    AlgebraicGeometry.Scheme.relativeProj.twistπ S m V ≫ S.toGradedAffineAlgebra.twistTransition m h =
      twistπSite S m W' :=
  CategoryTheory.comp_eq_of_heq_bridge (S.toGradedAffineAlgebra.twistπ_transition m h)
    (AlgebraicGeometry.Scheme.relativeProj.twistπ S m V) (S.toGradedAffineAlgebra.twistTransition m h)
    (twistπSite S m W') rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl

/-- Restriction is restriction of functions (`presheaf_map_apply`, one pushforward up): `(res y).1 p = y.1 (incl p)`. -/
theorem pushforward_twist_presheaf_map_apply {W' : X.AffineZariskiSite} (m : ℤ)
    {Ω Ω₀ : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens} (j : Ω ≤ Ω₀)
    (y : Γ(chartPush S m W', Ω₀))
    (p : (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading W')).Opens)) :
    Subtype.val ((chartPush S m W').presheaf.map (homOfLE j).op y :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W') m
          (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω)) p =
      Subtype.val (y : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W') m
          (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω₀))
        ⟨p.1, (S.toGradedAffineAlgebra.projChart W').preimage_mono j p.2⟩ := rfl

/-- **`twistπ V` sends the core of `evaluationLocal` back to `a/1`** (Stacks 01NR: `twistπ` is compatible with
`a ↦ a/1` on the chart): for `s ∈ Γ(Proj A(V), O(m))`, applying `relativeProj.twistπ S m V` to
`z = twistAffineIso.inv (unit s) ∈ Γ(O(m), ι''(φ⁻¹⊤))` gives `s` restricted to `c⁻¹(ι''(φ⁻¹⊤)) = ⊤`.

**Proof.** `twistAffineIso.hom = twistAffineHom` (`asIso_hom`), whose body is `A ≫ B ≫ C ≫ φ^*θ`
(`restrictFunctorIsoPullback`, `pullbackCongr`, `pullbackComp.inv`, and `θ = twistChartHom`, the adjoint transpose
of `twistπ`); apply `Modules.app_image_eq_of_iso_hom_heq_chartHomShape` (above; it combines `inv_hom_id` with
`RelativeProjEvaluationChart.app_image_eq_of_chartHomShape_heq`) with `k := relativeProj.twistπ S m V`; all bridge
arguments are `rfl` / `HEq.rfl`.

**Kernel time.** The cost is not in the `_proof_n` constants themselves but in the **different spellings of the
goal side and the body side**: `exact` first unifies the goal (`pushforward (projChart ⟨V.1, V.2⟩)` with implicit
arguments spelled `S.toGradedAffineAlgebra.relativeProj.left`, the literal proof `V.2`, and the `IsOpenImmersion`
instance synthesized in the statement) with the lemma's `Q P Y c hιOI`, while `hz`/`hI` need the spelling of the
body of `twistAffineHom` (`(relativeProj S).left`, `twistAffineHom._proof_n`). The two differ under
`NatTrans.app` / `Hom.app` / `ConcreteCategory.hom`, all of which are `abbrev`-hinted projection functions: the
kernel's `lazy_delta_reduction_step` compares arguments lazily only for `regular`-hinted constants; `abbrev` heads
are unfolded on both sides, and then a full `whnf` is run on the applied projection, which normalizes the whole
`restrictFunctorIsoPullback` (`leftAdjointUniq`) / adjunction machinery (measured 38–45 s;
`set_option diagnostics true` shows the kernel unfolding `DFunLike.coe` 840,000 times and
`HomogeneousLocalization.NumDenSameDeg` 100,000 times). Moreover `unfold … at h` / `dsimp only at h` only
**relabel** up to definitional equality (they produce no term), so the kernel still sees the folded form
`Hom.app (twistAffineHom …)`. Solution: the wrapper lemma duplicates every variable (the body side is unified
from `hIH := HEq.rfl` after `rw/unfold/dsimp`, the goal side from the goal) and bridges them only at the
**top level** by `rfl`/`HEq.rfl`; all bridges are written `by exact …` so that they are postponed until the body
side has been unified. The kernel time of the whole declaration then becomes unmeasurable. -/
theorem twistπ_app_twistAffineIso_inv_unit (m : ℕ) (V : X.affineOpens)
    (s : Γ(AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ), ⊤)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistπ S (m : ℤ) V).app
        (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ
          ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))
        (((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V (m : ℤ)).inv.app
            ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
                (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app
                (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ))).app ⊤).hom s)) =
      ((AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ)).presheaf.map
          (homOfLE (le_top : (S.toGradedAffineAlgebra.projChart ⟨V.1, V.2⟩) ⁻¹ᵁ
            (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ
              ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)) ≤ ⊤)).op s :
        Γ((AlgebraicGeometry.Scheme.Modules.pushforward (S.toGradedAffineAlgebra.projChart ⟨V.1, V.2⟩)).obj
            (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ)),
          ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ
            ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤))) :=
  AlgebraicGeometry.Scheme.Modules.app_image_eq_of_iso_hom_heq_chartHomShape
    (hφOI := AlgebraicGeometry.IsOpenImmersion.of_isIso (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom)
    (hcOI := S.toGradedAffineAlgebra.projChart_isOpenImmersion ⟨V.1, V.2⟩)
    (hc := affineIso_hom_comp_projChart S V) s (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V (m : ℤ))
    (AlgebraicGeometry.Scheme.relativeProj.twistπ S (m : ℤ) V) rfl
    (by
      -- body side: after `rw`/`unfold`/`dsimp` the elaborator sees the zeta-reduced body of `twistAffineHom`, and
      -- `HEq.rfl` unifies the body-side variables of the wrapper lemma with it (see its docstring)
      rw [twistAffineIso_hom]
      unfold AlgebraicGeometry.Scheme.relativeProj.twistAffineHom
      dsimp only
      exact HEq.rfl)
    -- bridges body side ↔ goal side, all postponed (`by exact`) until the body side has been unified
    (by exact rfl) (by exact rfl) (by exact rfl) (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    -- θ = twistChartHom = adjoint transpose of `GradedAffineAlgebra.twistπ`, bridged to `relativeProj.twistπ`
    (by exact HEq.rfl) (by exact rfl) (by exact rfl) (by exact HEq.rfl) (by exact HEq.rfl) (by exact HEq.rfl)
    (by exact HEq.rfl)

/-- **The pointwise value of `twistπ W′` on the restriction of `evaluationLocal V x`**: for `W′ ≤ V` (a principal
open) and `Ω ≤ π⁻¹V`, the value of `(twistπ m W′).app Ω (evaluationLocal S m V x |_Ω)` at `p ∈ c_{W′}⁻¹Ω` is
`(res_{W′←V} a)/1`, where `a = sectionsOf V m x`.

The proof has three steps: (1) `twistπ m W′ = twistπ m V ≫ θ` (`twistπ_comp_twistTransition`) and the naturality
of `twistπ` reduce the claim to `twistπ m V` applied to the core `z = twistAffineIso.inv (unit (a/1))` of
`evaluationLocal`; (2) **`twistπ V` sends the core back to `a/1`**: `twistAffineHom z = unit (a/1)` (`inv_hom_id`),
then the general lemma `app_image_eq_of_chartHomShape_heq` of `RelativeProjEvaluationChart`, whose hypothesis `hz`
is the body of `twistAffineHom` (`unfold`; all data of the lemma are unified from that hypothesis, see its
docstring), with all bridge arguments `rfl` / `HEq.rfl`; (3) the pointwise formula `a/1 ↦ (res a)/1` for `θ`
(`twistPushTransition_apply_of_val`; the pointwise value `a/1` holds by definition). -/
theorem twistπ_app_res_evaluationLocal (m : ℕ) (V : X.affineOpens) {W' : X.AffineZariskiSite}
    (h : W' ≤ AlgebraicGeometry.Scheme.affineSite V) {Ω : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens}
    (hΩ : Ω ≤ (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1) (x : Γ(S.part m, V.1))
    (p : (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω :
      (AlgebraicGeometry.Proj (S.toGradedAffineAlgebra.grading W')).Opens)) :
    Subtype.val (((twistπSite S (m : ℤ) W').app Ω).hom
        ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map (homOfLE hΩ).op
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x)) :
        MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule (S.toGradedAffineAlgebra.grading W') (m : ℤ)
          (S.toGradedAffineAlgebra.projChart W' ⁻¹ᵁ Ω)) p =
      Localization.mk (S.toGradedAffineAlgebra.restrictGraded h (S.sectionsOf V.1 m x).1) 1 := by
  rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq]
  erw [AlgebraicGeometry.Scheme.Modules.presheaf_map_map_homOfLE]
  set s := AlgebraicGeometry.Proj.twistSection (S.sectionsGrading V.1)
    (S.sectionsOf V.1 m x).1 (S.sectionsOf V.1 m x).2 with hs
  set z := (((AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V (m : ℤ)).inv.app
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
              (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).unit.app
              (AlgebraicGeometry.Proj.twist (S.sectionsGrading V.1) (m : ℤ))).app ⊤).hom s)) with hz
  set j := hΩ.trans (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_le S V) with hj
  -- (1) naturality of `twistπ W′`, then `twistπ W′ = twistπ V ≫ θ`
  have hnat : ((twistπSite S (m : ℤ) W').app Ω).hom
      ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map (homOfLE j).op z) =
      (chartPush S (m : ℤ) W').presheaf.map (homOfLE j).op (((twistπSite S (m : ℤ) W').app _).hom z) :=
    ConcreteCategory.congr_hom ((twistπSite S (m : ℤ) W').mapPresheaf.naturality (homOfLE j).op) z
  erw [hnat]
  rw [pushforward_twist_presheaf_map_apply, ← twistπ_comp_twistTransition S (m : ℤ) V h]
  erw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  -- (2) `twistπ V` sends the core `z` back to (the restriction of) `a/1` (named leaf, see its docstring)
  erw [twistπ_app_twistAffineIso_inv_unit S m V s]
  -- (3) θ pointwise: `a/1 ↦ (res a)/1`
  exact AlgebraicGeometry.Proj.twistPushTransition_apply_of_val (S.toGradedAffineAlgebra.restrictGraded h)
    (S.toGradedAffineAlgebra.restrict_irrelevant_le h) (m : ℤ) (S.sectionsOf V.1 m x).1
    (S.toGradedAffineAlgebra.projChart (AlgebraicGeometry.Scheme.affineSite V))
    (S.toGradedAffineAlgebra.projChart W') (S.toGradedAffineAlgebra.map_projChart h) _ _ (fun q => rfl) _

/-- The limit projection `twistπ m W′` is injective on the image of the chart `W′` (Stacks 01LI,
`isIso_restrictFunctor_map_twistπ`). -/
theorem twistπSite_app_image_top_injective (m : ℤ) (W' : X.AffineZariskiSite) :
    Function.Injective ((twistπSite S m W').app (S.toGradedAffineAlgebra.projChart W' ''ᵁ ⊤)).hom := by
  have h2 : IsIso (((AlgebraicGeometry.Scheme.Modules.restrictFunctor (S.toGradedAffineAlgebra.projChart W')).map
      (S.toGradedAffineAlgebra.twistπ m W')).app ⊤) :=
    AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (S.toGradedAffineAlgebra.isIso_restrictFunctor_map_twistπ m W') ⊤
  have h3 : IsIso ((S.toGradedAffineAlgebra.twistπ m W').app (S.toGradedAffineAlgebra.projChart W' ''ᵁ ⊤)) := by
    rw [← AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_app_image]; exact h2
  have h4 : IsIso ((twistπSite S m W').app (S.toGradedAffineAlgebra.projChart W' ''ᵁ ⊤)) := h3
  letI := h4
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- `sectionsOf` is compatible with restriction: `sectionsOf W m (x|_W) = res_{W←V} (sectionsOf V m x)`
(`DirectSum.of` componentwise). -/
theorem sectionsOf_res {V W : X.Opens} (h : W ≤ V) (m : ℕ) (x : Γ(S.part m, V)) :
    ((S.sectionsOf W m ((S.part m).presheaf.map (homOfLE h).op x) : S.sectionsGrading W m) : S.sectionsRing W) =
      S.sectionsRestrict h ((S.sectionsOf V m x : S.sectionsGrading V m) : S.sectionsRing V) := by
  show DirectSum.of (S.sectionsPiece W) m _ = S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece V) m x)
  exact (S.sectionsRestrictRingHom_of h m x).symm

/-- **Naturality on the basis, sectionwise**: for affine opens `W ≤ V`,
`evaluationLocal W (x|_W) = (evaluationLocal V x)|_{π⁻¹W}`. -/
theorem evaluationLocal_restrict (m : ℕ) (V W : X.affineOpens) (h : W.1 ≤ V.1) (x : Γ(S.part m, V.1)) :
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m W ((S.part m).presheaf.map (homOfLE h).op x) =
      (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map
        (homOfLE ((AlgebraicGeometry.Scheme.relativeProj S).hom.preimage_mono h)).op
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) := by
  set π := (AlgebraicGeometry.Scheme.relativeProj S).hom with hπ
  set A := S.toGradedAffineAlgebra with hA
  let Idx := {W' : X.AffineZariskiSite //
    W' ≤ AlgebraicGeometry.Scheme.affineSite W ∧ W' ≤ AlgebraicGeometry.Scheme.affineSite V}
  let Ω : Idx → (AlgebraicGeometry.Scheme.relativeProj S).left.Opens := fun i => A.projChart i.1 ''ᵁ ⊤
  have hΩ : ∀ i : Idx, Ω i ≤ π ⁻¹ᵁ W.1 := fun i => by
    show A.projChart i.1 ''ᵁ ⊤ ≤ _
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange, ← A.proj_preimage_eq_opensRange]
    exact π.preimage_mono (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono i.2.1)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨(AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf,
    (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).isSheaf⟩ Ω (π ⁻¹ᵁ W.1)
    (fun i => homOfLE (hΩ i)) ?_ _ _ ?_
  · intro q hq
    have hπq : π q ∈ W.1 := hq
    obtain ⟨f, hfW, hqf⟩ := V.2.exists_basicOpen_le (V := W.1) ⟨π q, hπq⟩ (h hπq)
    let W' : X.AffineZariskiSite :=
      AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen (AlgebraicGeometry.Scheme.affineSite V) f
    have hW'V : W' ≤ AlgebraicGeometry.Scheme.affineSite V :=
      AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le _ f
    have hW'W : W' ≤ AlgebraicGeometry.Scheme.affineSite W := by
      refine ⟨X.presheaf.map (homOfLE h).op f, ?_⟩
      show X.basicOpen (X.presheaf.map (homOfLE h).op f) = X.basicOpen f
      rw [X.basicOpen_res f (homOfLE h).op]
      exact inf_eq_right.mpr hfW
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W', hW'W, hW'V⟩, ?_⟩
    show q ∈ A.projChart W' ''ᵁ ⊤
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange, ← A.proj_preimage_eq_opensRange]
    exact hqf
  · intro i
    apply twistπSite_app_image_top_injective S (m : ℤ) i.1
    refine Subtype.ext (funext fun p => ?_)
    have e2 : (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map (homOfLE (hΩ i)).op
        ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map (homOfLE (π.preimage_mono h)).op
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x)) =
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).presheaf.map
          (homOfLE ((hΩ i).trans (π.preimage_mono h))).op
          (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) :=
      AlgebraicGeometry.Scheme.Modules.presheaf_map_map_homOfLE _ _ _ _
    rw [e2]
    refine (twistπ_app_res_evaluationLocal S m W i.2.1 (hΩ i) _ p).trans
      ((twistπ_app_res_evaluationLocal S m V i.2.2 ((hΩ i).trans (π.preimage_mono h)) x p).trans ?_).symm
    congr 1
    rw [sectionsOf_res]
    exact (congrArg (fun φ : S.sectionsGrading V.1 →+*ᵍ A.grading i.1 => φ (S.sectionsOf V.1 m x).1)
      (AlgebraicGeometry.Scheme.relativeProj.restrictGraded_comp_sectionsRestrict S i.2.1 i.2.2 h)).symm

end AlgebraicGeometry.Scheme.relativeProj

/-- `evaluationLocal` is natural on the basis of affine opens: for affine `W ≤ V`, evaluating and then
restricting equals restricting and then evaluating.

Source: Stacks 01NQ (the gluing data of the affine pieces of `relativeProj`), 01NR (`twistAffineIso` is
compatible with restriction), 01MN (`Proj.twistSection` is compatible with `A(V) → A(W)`).

Proof sketch (`evaluationLocal_restrict`): both sides are sections of `Γ(O(m), π⁻¹W)`. Instead of the
injectivity of `twistAffineHom W`, use that the limit projection `twistπ m W′` is injective on the image of
the chart `W′` (Stacks 01LI, `isIso_restrictFunctor_map_twistπ`), where `W′ = D_V(f) ⊆ W` is simultaneously a
principal open of `V` and of `W` (`IsAffineOpen.exists_basicOpen_le`, the same construction as
`exists_projMap_restrictGraded_eq`). On `π⁻¹W′` both sides are reduced, via `twistπ_transition`
(`twistπ W′ = twistπ V ≫ θ`) and "`twistπ V` sends the core of `evaluationLocal` back to `a/1`"
(`twistπ_app_twistAffineIso_inv_unit`), to the pointwise formula `a/1 ↦ (res a)/1` for `θ`; they agree by
`restrictGraded_comp_sectionsRestrict`; finally glue with `TopCat.Sheaf.eq_of_locally_eq'`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationBase_naturality
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ)
    {V W : (CategoryTheory.InducedCategory X.Opens (fun V : X.affineOpens => V.1))ᵒᵖ} (f : V ⟶ W) :
    ((CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙
          (S.part m).presheaf).map f ≫
        AlgebraicGeometry.Scheme.relativeProj.evaluationBaseApp S m W =
      AlgebraicGeometry.Scheme.relativeProj.evaluationBaseApp S m V ≫
        ((CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙
          ((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf).map f := by
  ext x
  exact AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_restrict S m V.unop W.unop
    (leOfHom ((CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).map f.unop)) x

/-- The natural transformation on the basis of affine opens from which `evaluation` is extended. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.evaluationBase
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) :
    (CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙ (S.part m).presheaf ⟶
      (CategoryTheory.inducedFunctor (fun V : X.affineOpens => V.1)).op ⋙
        ((AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf where
  app V := AlgebraicGeometry.Scheme.relativeProj.evaluationBaseApp S m V
  naturality _ _ f := AlgebraicGeometry.Scheme.relativeProj.evaluationBase_naturality S m f

/-- The affine opens form a basis of the topology of `X`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isBasis_affineOpens_val
    {X : AlgebraicGeometry.Scheme.{u}} :
    TopologicalSpace.Opens.IsBasis (Set.range (fun V : X.affineOpens => V.1)) := by
  rw [Subtype.range_coe]; exact X.isBasis_affineOpens

/-- The presheaf morphism `S_m.presheaf ⟶ (π_*O(m)).presheaf` extended from the basis (Mathlib
`restrictHomEquivHom`). -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) :
    (S.part m).presheaf ⟶
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom (S.part m).presheaf
    ⟨((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf,
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).isSheaf⟩
    AlgebraicGeometry.Scheme.relativeProj.isBasis_affineOpens_val
    (AlgebraicGeometry.Scheme.relativeProj.evaluationBase S m)

/-- The components of `evaluationBase` act on sections as `evaluationLocal` (a definitional equality; bridge
lemma). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationBase_app_apply
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ)
    (V : (CategoryTheory.InducedCategory X.Opens (fun V : X.affineOpens => V.1))ᵒᵖ)
    (x : Γ(S.part m, V.unop.1)) :
    (AlgebraicGeometry.Scheme.relativeProj.evaluationBase S m).app V x =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V.unop x := rfl

/-- On an affine open `V`, the presheaf morphism extended from the basis is `evaluationBase` (Mathlib
`TopCat.Sheaf.extend_hom_app`). The sheaf `F'` must be given explicitly: leaving `_` makes the unifier `whnf`
`?F'.val =?= Modules.presheaf (π_*O(m))`, which times out. -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_app_affine
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens) :
    (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).app (Opposite.op V.1) =
      (AlgebraicGeometry.Scheme.relativeProj.evaluationBase S m).app (Opposite.op V) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom
  exact TopCat.Sheaf.extend_hom_app (S.part m).presheaf
    ⟨((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf,
      ((AlgebraicGeometry.Scheme.Modules.pushforward
        (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).isSheaf⟩
    AlgebraicGeometry.Scheme.relativeProj.isBasis_affineOpens_val
    (AlgebraicGeometry.Scheme.relativeProj.evaluationBase S m) V

/-- **`O_X`-linearity on the basis**: on an affine open `V`,
`evaluationLocal S m V (r • x) = r • evaluationLocal S m V x`, where `r •` on the right is the scalar action of
`Γ(X, V)` on `Γ(π_*O(m), V) = Γ(O(m), π⁻¹V)` (by definition of the pushforward module, `π^♯(r) • —`).

Source: Stacks 01MN (`A_m → Γ(Proj A, O(m))` is `A_0`-linear: `a ↦ a/1` and `r·a ↦ (r/1)·(a/1)`); 01NQ/01NR
provide `π⁻¹V ≅ Proj A(V)` and `O(m)|_{π⁻¹V} ≅ O_{Proj A(V)}(m)`.

Proof, following the five steps of `evaluationLocal`:
(1) `sectionsUnit_mul_of`: `sectionsOf V m (r • x) = sectionsUnit V r * sectionsOf V m x` in
`A(V) = ⊕_k Γ(V, S_k)`;
(2) `Proj.twistSection_smul`: `twistSection (u * a) = ũ • twistSection a` whenever `ũ` is pointwise `u/1`
(`u ∈ A(V)_0`); the module structure of `sectionsSubmodule` is pointwise multiplication;
(3) `ũ := structureSection S V r` (`RelativeProjEvaluationScalar`): it is `(toSpecZero ≫ Spec.map (sectionsUnit V))^♯`
applied to `ΓSpecIso⁻¹ r`; its pointwise value `(sectionsUnit V r)/1` is `structureSection_apply_val`
(`toSpecZero = toSpecΓ ≫ Spec.map zeroToGlobal` and `awayToSection_apply`), and `φ^♯ ũ = ι^♯ (π^♯ r)` is
`affineIso_hom_app_structureSection` (`ι ≫ π = φ ≫ chartToOpen ≫ V.ι`,
`chartToOpen ≫ V.ι = (toSpecZero ≫ Spec.map (sectionsUnit V)) ≫ fromSpec`, `fromSpec.appLE V ⊤ = ΓSpecIso⁻¹`);
(4)(5) `Modules.Hom.app_smul` (adjunction unit, `twistAffineIso.inv`), `pushforward_smul_def'` (the pushforward
action goes through `φ^♯`), `restrict_appLE_smul` (on the restricted sheaf the action of `ι.appLE _ _ c` is the
action of `c|_{ι''W}`), `Modules.map_smul`, and `presheaf_map_map_of_le_le` (restricting back and forth between
`π⁻¹V = ι''(φ⁻¹⊤)` is the identity). -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_smul
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (V : X.affineOpens)
    (r : Γ(X, V.1)) (x : Γ(S.part m, V.1)) :
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V (r • x) =
      @HSMul.hSMul Γ(X, V.1)
        Γ((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)), V.1)
        Γ((AlgebraicGeometry.Scheme.Modules.pushforward
            (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)), V.1)
        instHSMul r (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S m V x) := by
  have e1 : ((S.sectionsOf V.1 m (r • x) : S.sectionsGrading V.1 m) : S.sectionsRing V.1) =
      ((S.sectionsUnit V.1 r : S.sectionsGrading V.1 0) : S.sectionsRing V.1) *
        ((S.sectionsOf V.1 m x : S.sectionsGrading V.1 m) : S.sectionsRing V.1) :=
    (S.sectionsUnit_mul_of V.1 r x).symm
  have hle : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ''ᵁ
      ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) ≤
      (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1 := by
    rw [AlgebraicGeometry.Scheme.Hom.preimage_top, AlgebraicGeometry.Scheme.Opens.ι_image_top]
  rw [AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_eq,
    AlgebraicGeometry.Proj.twistSection_smul (S.sectionsGrading V.1) (S.sectionsOf V.1 m x).2 _ e1
      (AlgebraicGeometry.Scheme.relativeProj.structureSection S V r)
      (AlgebraicGeometry.Scheme.relativeProj.structureSection_apply_val S V r)]
  erw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  rw [AlgebraicGeometry.Scheme.Modules.pushforward_smul_def'
      (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom _ ⊤]
  erw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  rw [AlgebraicGeometry.Scheme.relativeProj.affineIso_hom_app_structureSection]
  erw [AlgebraicGeometry.Scheme.Modules.restrict_appLE_smul _ _ _ hle]
  erw [AlgebraicGeometry.Scheme.Modules.map_smul]
  erw [AlgebraicGeometry.Scheme.presheaf_map_map_of_le_le]
  rfl

/-- The extended presheaf morphism is `O_X`-linear.

Source: Stacks 01O4 (the evaluation is a morphism of modules).

Proof: on the basis this is `evaluationLocal_smul`. On a general open `W`, cover `W` by the affine opens
`{V : X.affineOpens // V.1 ≤ W}` (`X.isBasis_affineOpens`, `Opens.isBasis_iff_nbhd`) and use
`TopCat.Sheaf.eq_of_locally_eq'`; on each `V` the restrictions of both sides agree by the naturality of
`evaluationPresheafHom`, `Scheme.Modules.map_smul` (on both sides), `evaluationPresheafHom_app_affine` (on the
basis the morphism is `evaluationBase`) and `evaluationLocal_smul`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_smul
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) :
    ∀ (V : X.Opens) (r : Γ(X, V)) (s : Γ(S.part m, V)),
      (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).app (Opposite.op V) (r • s) =
        r • (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).app (Opposite.op V) s := by
  intro W r s
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf,
      ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} => i.1.1) W (fun i => CategoryTheory.homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    have nat := fun y => CategoryTheory.ConcreteCategory.congr_hom
      ((AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).naturality
        (CategoryTheory.homOfLE i.2).op) y
    simp only [CategoryTheory.ConcreteCategory.comp_apply] at nat
    change ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf.map
          (CategoryTheory.homOfLE i.2).op
        ((AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).app (Opposite.op W) (r • s)) =
      ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ))).presheaf.map
          (CategoryTheory.homOfLE i.2).op
        (r • (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m).app (Opposite.op W) s)
    rw [← nat, AlgebraicGeometry.Scheme.Modules.map_smul, AlgebraicGeometry.Scheme.Modules.map_smul,
      ← nat, AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_app_affine S m i.1,
      AlgebraicGeometry.Scheme.relativeProj.evaluationBase_app_apply,
      AlgebraicGeometry.Scheme.relativeProj.evaluationBase_app_apply,
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal_smul]

/-- The canonical evaluation of a relative Proj, `π^*S_m → O(m)` (the universal element of
`f^*𝒜_n → ℒ^{⊗n}` in Stacks 01O4). Under the adjunction `pullback ⊣ pushforward` it corresponds to
`S_m → π_*O(m)`, which is given piecewise on the basis of affine opens of `X`: on an affine `V`,
`Γ(S_m, V) → A(V)_m` (`sectionsOf`) `→ Γ(Proj A(V), O(m))` (`a ↦ a/1`, `Proj.twistSection`, Stacks 01MN)
`→ Γ(π⁻¹V, φ_V^*O(m))` (pullback along `φ_V : π⁻¹V ≅ Proj A(V)`, adjunction unit)
`→ Γ(π⁻¹V, O(m))` (`twistAffineIso`, Stacks 01NR), and then extended from the basis to a morphism of sheaves
with Mathlib's `restrictHomEquivHom`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.evaluation {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj (S.part m)
      ⟶ AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (AlgebraicGeometry.Scheme.relativeProj S).hom).homEquiv _ _).symm
    (SheafOfModules.Hom.mk (PresheafOfModules.homMk
      (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m)
      (fun V r s =>
        AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_smul S m V.unop r s)))

/-- `φ : g^*S_m → M` is *induced by* `τ`: `g = τ ≫ π`, and `φ` factors through `g^*S_m ≅ τ^*π^*S_m` as
`τ^*(evaluation)` followed by some `ψ : τ^*O(m) → M`. -/
def AlgebraicGeometry.Scheme.relativeProj.InducedBy {X T : AlgebraicGeometry.Scheme.{u}}
    {S : X.GradedQCAlgebra} {m : ℕ} (τ : T ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left)
    {M : T.Modules}
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback (τ ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom)).obj
      (S.part m) ⟶ M) : Prop :=
  ∃ ψ : (AlgebraicGeometry.Scheme.Modules.pullback τ).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) ⟶ M,
    φ = (AlgebraicGeometry.Scheme.Modules.pullbackComp τ (AlgebraicGeometry.Scheme.relativeProj S).hom).inv.app _
      ≫ (AlgebraicGeometry.Scheme.Modules.pullback τ).map
          (AlgebraicGeometry.Scheme.relativeProj.evaluation S m) ≫ ψ

end
