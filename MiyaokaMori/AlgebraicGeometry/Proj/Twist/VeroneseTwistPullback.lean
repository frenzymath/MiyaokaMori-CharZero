import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjVeroneseIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackChartIsoNatural

/-! # The Veronese isomorphism identifies the pullback of `O(1)` with `O(m)`

Statement: for a positive integer `m`, the relative Veronese isomorphism `Proj_X(S^(m)) ≅ Proj_X(S)` identifies the
pullback of `O(1)` with `O(m)`.

Sources: Lemma 2.2 of the paper ("a Veronese does not change relative Proj … `O(1)` restricts
to `O(m)`"); Stacks 0B5J, 01NR.

## Route

Write `ψ := veroneseIso.leftIso S m hm : Proj_X S^(m) ≅ Proj_X S` (so `(veroneseIso S m hm).inv.left = ψ.inv`
definitionally, `Over.isoMk`). Both twists are limits of their gluing diagrams
(`GradedAffineAlgebra.twist_eq_limit`, `RelativeProjTwistLimit`):
`O_{Proj_X S}(m) = lim_U (c_U)_* O_{Proj S(U)}(m)` and `O_{Proj_X S^(m)}(1) = lim_U (c'_U)_* O_{Proj S^(m)(U)}(1)`,
where `c_U`, `c'_U` are the affine charts `projChart U`.

1. `ψ.inv^* ≅ (ψ.hom)_*` (`Modules.pullbackIsoPushforwardInv`): both are left adjoint to `(ψ.inv)_*`, and
   `(ψ.hom)_*`, `(ψ.inv)_*` form an equivalence because `pushforward` is functorial up to natural
   isomorphism (`pushforwardComp`, `pushforwardCongr`, `pushforwardId`).
2. `(ψ.hom)_*` is a right adjoint, so it preserves the limit: `(ψ.hom)_* O(1) ≅ lim_U (ψ.hom)_* (c'_U)_* O_{Proj S^(m)(U)}(1)`
   (Mathlib `preservesLimitIso`).
3. The two diagrams are isomorphic as functors on `X.AffineZariskiSiteᵒᵖ`: `veroneseIso.twistDiagram_iso_nonempty`.
   This is built from
   - the chart square `c'_U ≫ ψ.hom = e_U.hom ≫ c_U` (`projChart_comp_leftIso_hom`),
   - the component isomorphisms `(ψ.hom)_* (c'_U)_* T' ≅ (c_U)_* (e_U.hom)_* T'` (`twistChartPushIso`),
   - step 3a, `(Proj.map ofVeronese)_* O(1) ≅ O_{Proj A(U)^{(m)}}(1)` (`VeroneseTwistPullbackTwistToPushforwardIso`),
     packaged as `chartTwistPushIsoVeronese`,
   - and `veroneseTwistChartIso_exists`: the degree-rescaling isomorphisms
     `Ψ_U : ((Proj.veroneseIso A(U) m).hom)_* O_{Proj A(U)^{(m)}}(1) ≅ O_{Proj A(U)}(m)`
     (Stacks 0B5J; `chartTwistHom`, `VeroneseTwistPullbackVeroneseComparison`, hypotheses from
     `VeroneseTwistPullbackVeroneseHomApp`) together with their compatibility with the transition maps
     (`twistDiagramComponentIso_natural`, `VeroneseTwistPullbackChartIsoNatural`). The chart-level components live
     in `VeroneseTwistPullbackComponents`.
4. `HasLimit.isoOfNatIso` glues 1–3 into the statement.

Typing note: `GradedAffineAlgebra.twistDiagram` is typed in `(GradedAffineAlgebra.relativeProj _).left.Modules`,
while `relativeProj.twist` and `ψ` live in `(Scheme.relativeProj _).left.Modules`. These coincide only after
unfolding the `def Scheme.relativeProj`, which typeclass search does not do (it rejects even `?F := F` when the
category arguments differ syntactically). The alias `relativeProj.twistDiagram` below restates the diagram in the
Scheme-level category so that `HasLimit` / `PreservesLimit` instances are found.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- Bridge lemma (variable level), four-morphism version of `comp_eq_of_heq_bridge`
(`RelativeProjTwistComp`): `f ≫ g = k ≫ l` rewritten in another spelling `f' ≫ g' = k' ≫ l'`.
Objects and morphisms are variables; the concrete spellings are identified by top-level `rfl` / `HEq.rfl`, so the
kernel checks the definitional unfolding (`twistDiagram.map f = twistTransition …`) on small terms instead of
unfolding `CategoryStruct.comp` on the whole statement. The objects `A' B' D' E'` are **explicit** so that the caller
can spell them exactly as in its goal: `CategoryStruct.comp` has `abbrev` reducibility hints, and the kernel unfolds
it (rather than comparing arguments) as soon as one object is spelled differently (measured: 16 s per spelling
difference in the assembly below). -/
theorem comp_eq_comp_of_heq_bridge {A B D E : C} {f : A ⟶ B} {g : B ⟶ D} {k : A ⟶ E} {l : E ⟶ D}
    (h : f ≫ g = k ≫ l) (A' B' D' E' : C) (f' : A' ⟶ B') (g' : B' ⟶ D') (k' : A' ⟶ E') (l' : E' ⟶ D')
    (hA : A' = A) (hB : B' = B) (hD : D' = D) (hE : E' = E)
    (hf : HEq f' f) (hg : HEq g' g) (hk : HEq k' k) (hl : HEq l' l) : f' ≫ g' = k' ≫ l' := by
  subst hA; subst hB; subst hD; subst hE
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq hl
  exact h

/-- Bridge lemma for a functor applied to two spellings of the same morphism: the kernel checks `HEq a' a` on the
small inner terms instead of unfolding `G.map` (for `G = pushforward _` that unfolding costs 25 s). -/
theorem Functor.map_heq_bridge {D : Type u₁} [Category.{v₁} D] (G : C ⥤ D) {A B A' B' : C}
    (a : A ⟶ B) (a' : A' ⟶ B') (hA : A' = A) (hB : B' = B) (ha : HEq a' a) : HEq (G.map a') (G.map a) := by
  subst hA; subst hB
  obtain rfl := eq_of_heq ha
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- For an isomorphism of schemes `e : X ≅ Y`, the pushforwards `e.inv_* : Y.Modules ⥤ X.Modules` and
`e.hom_* : X.Modules ⥤ Y.Modules` form an equivalence of categories: `e.inv_* ⋙ e.hom_* ≅ (e.inv ≫ e.hom)_* = (𝟙)_* ≅ 𝟭`
and symmetrically (Mathlib `pushforwardComp`, `pushforwardCongr`, `pushforwardId`). -/
def pushforwardEquivOfIso {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.inv) (pushforward e.hom)
    ((pushforwardId Y).symm ≪≫ pushforwardCongr e.inv_hom_id.symm ≪≫ (pushforwardComp e.inv e.hom).symm)
    (pushforwardComp e.hom e.inv ≪≫ pushforwardCongr e.hom_inv_id ≪≫ pushforwardId X)

/-- Pullback along an isomorphism of schemes is naturally isomorphic to pushforward along its inverse:
`e.hom^*` and `e.inv_*` are both left adjoint to `e.hom_*` (`pullbackPushforwardAdjunction` and the adjunction
of the equivalence `pushforwardEquivOfIso e`), and left adjoints are unique (`Adjunction.leftAdjointUniq`). -/
def pullbackIsoPushforwardInv {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y) :
    pullback e.hom ≅ pushforward e.inv :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction e.hom)
    (pushforwardEquivOfIso e).toAdjunction

end AlgebraicGeometry.Scheme.Modules

/-- The gluing diagram `U ↦ (c_U)_* O_{Proj S(U)}(m)` of `O_{Proj_X S}(m)` (`RelativeProjTwistLimit`,
`GradedAffineAlgebra.twistDiagram`), retyped in the Scheme-level category `(Scheme.relativeProj S).left.Modules`.
Definitionally equal to `S.toGradedAffineAlgebra.twistDiagram m`; the alias exists only so that typeclass search
sees the same category as `relativeProj.twist S m` (see the module docstring). -/
def AlgebraicGeometry.Scheme.relativeProj.twistDiagram {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℤ) :
    X.AffineZariskiSiteᵒᵖ ⥤ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules :=
  S.toGradedAffineAlgebra.twistDiagram m

/-- `O_{Proj_X S}(m)` is the limit of its gluing diagram, stated in the Scheme-level category
(`GradedAffineAlgebra.twist_eq_limit` transported along the definitional unfoldings of the `abbrev`
`relativeProj.twist` and of `relativeProj.twistDiagram`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.twist_eq_limit_twistDiagram
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℤ) :
    haveI : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules :=
      SheafOfModules.hasLimitsOfShape _ _
    AlgebraicGeometry.Scheme.relativeProj.twist S m =
      limit (AlgebraicGeometry.Scheme.relativeProj.twistDiagram S m) :=
  S.toGradedAffineAlgebra.twist_eq_limit m

namespace AlgebraicGeometry.Scheme.relativeProj.veroneseIso

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m)

/-- There is a family of isomorphisms
`Ψ_U : ((Proj.veroneseIso A(U) m hm).hom)_* O_{Proj A(U)^{(m)}}(1) ≅ O_{Proj A(U)}(m)` (`U` affine open of `X`)
such that the resulting components `twistDiagramComponentIso Ψ U` commute with the transition maps
`twistTransition` of the two gluing diagrams (pushed forward along `ψ.hom` on the left).

Source: Stacks 0B5J (the Veronese isomorphism `Proj S ≅ Proj S^{(d)}` and the identification of the twists
`O_{Proj S}(nd) ↔ O_{Proj S^{(d)}}(n)` that goes with it); Stacks 01MX (θ), 01NP (transition maps);
Lemma 2.2 of the paper.

Proof:
* `Ψ_U := asIso (chartTwistHom U)`, where `chartTwistHom U = Proj.veroneseTwistHom …` is the degree-rescaling comparison
  morphism `((veroneseIso).hom)_* O_{B(U)}(1) ⟶ O_{A(U)}(m)`, pointwise `s ↦ (𝔭 ↦ (B(U)_{𝔭 ∩ B(U)} → A(U)_𝔭)(s(veroneseHom 𝔭)))`
  (`VeroneseTwistPullbackVeroneseComparison`). Its hypotheses for `φ = veroneseHom`, `ψ = (veroneseIso).hom` are
  supplied by `VeroneseTwistPullbackVeroneseHomApp`: the pointwise description of `veroneseHom` on points
  (`Stacks0b5j`) and on structure-sheaf sections.
* `IsIso (chartTwistHom U)` is `Proj.isIso_veroneseTwistHom`, from the bijectivity on every open
  (injectivity and surjectivity `veroneseTwistHom_app_surjective`).
* The compatibility with the transition maps is `twistDiagramComponentIso_natural`
  (`VeroneseTwistPullbackChartIsoNatural`), applied with `hΨ U := rfl` (`asIso_hom`).
The choice of `Ψ` happens inside this proof of a proposition, so no definition takes data from a proposition.
The choice of `Ψ` happens inside this proof of a proposition, so no definition takes data from an unproved proposition.

Edge cases: `X = ∅` or `Proj_X S = ∅` — the index category is still `X.AffineZariskiSite` (possibly with only `⊥`),
every chart is empty and every module involved is `0`; `m = 1`: `B(U) = A(U)` with relabelled pieces. -/
theorem veroneseTwistChartIso_exists :
    ∃ Ψ : ∀ U : X.AffineZariskiSite,
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Proj.veroneseIso (S.sectionsGrading U.toOpens) m hm).hom).obj
        (AlgebraicGeometry.Proj.twist (veroneseGrading (S.sectionsGrading U.toOpens) m) 1) ≅
      AlgebraicGeometry.Proj.twist (S.sectionsGrading U.toOpens) (m : ℤ),
    ∀ {U V : X.AffineZariskiSite} (h : U ≤ V),
      (AlgebraicGeometry.Scheme.Modules.pushforward (leftIso S m hm).hom).map
          ((S.veronese m).toGradedAffineAlgebra.twistTransition 1 h) ≫
        (twistDiagramComponentIso S m hm Ψ U).hom =
      (twistDiagramComponentIso S m hm Ψ V).hom ≫ S.toGradedAffineAlgebra.twistTransition (m : ℤ) h := by
  have hiso : ∀ U : X.AffineZariskiSite, IsIso (chartTwistHom S m hm U) := fun U =>
    AlgebraicGeometry.Proj.isIso_veroneseTwistHom _ _ _
      (AlgebraicGeometry.Proj.veroneseHom_base_veroneseIso_hom_base (S.sectionsGrading U.toOpens) m hm) hm 1 (m : ℤ)
      (one_mul _).symm
  refine ⟨fun U => @asIso _ _ _ _ (chartTwistHom S m hm U) (hiso U), fun {U V} h => ?_⟩
  exact twistDiagramComponentIso_natural S m hm _ (fun U => rfl) h

end AlgebraicGeometry.Scheme.relativeProj.veroneseIso

/-- The gluing diagram of `O_{Proj_X S^(m)}(1)`, pushed forward along `ψ := veroneseIso.leftIso S m hm`, is isomorphic
to the gluing diagram of `O_{Proj_X S}(m)`, as functors on `X.AffineZariskiSiteᵒᵖ`.

Source: Stacks 0B5J; Stacks 01MX (θ), 01NP (transition maps); Lemma 2.2 of the paper.

Constructed by `NatIso.ofComponents` from the components `twistDiagramComponentIso` — chart square
(`projChart_comp_leftIso_hom`), `pushforwardComp`/`pushforwardCongr` (`twistChartPushIso`), step 3a
(`chartTwistPushIsoVeronese`, module VeroneseTwistPullbackTwistToPushforwardIso) — and the leaf
`veroneseTwistChartIso_exists` (degree-rescaling isomorphisms `Ψ_U` and their compatibility with the transition maps).
The naturality condition of `NatIso.ofComponents` is, after unfolding `twistDiagram`, exactly the compatibility in the leaf
(`(twistDiagram _ _).map f = twistTransition _ (leOfHom f.unop)` definitionally). -/
theorem AlgebraicGeometry.Scheme.relativeProj.veroneseIso.twistDiagram_iso_nonempty
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m) :
    Nonempty (AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ) ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom ≅
      AlgebraicGeometry.Scheme.relativeProj.twistDiagram S (m : ℤ)) := by
  obtain ⟨Ψ, hΨ⟩ := AlgebraicGeometry.Scheme.relativeProj.veroneseIso.veroneseTwistChartIso_exists S m hm
  exact ⟨NatIso.ofComponents
    (fun U => AlgebraicGeometry.Scheme.relativeProj.veroneseIso.twistDiagramComponentIso S m hm Ψ U.unop)
    (fun {U V} f => comp_eq_comp_of_heq_bridge (hΨ (leOfHom f.unop))
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ) ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom).obj U)
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ) ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom).obj V)
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram S (m : ℤ)).obj V)
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram S (m : ℤ)).obj U)
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ) ⋙
        AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom).map f)
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.twistDiagramComponentIso S m hm Ψ V.unop).hom
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.twistDiagramComponentIso S m hm Ψ U.unop).hom
      ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram S (m : ℤ)).map f)
      rfl rfl rfl rfl
      -- `(D' ⋙ ψ_*).map f = ψ_*.map (D'.map f)` (`Functor.comp_map`), then `D'.map f ≡ twistTransition …` under `ψ_*.map`
      -- through `Functor.map_heq_bridge`: the kernel never unfolds `pushforward` (see the bridge lemmas above).
      ((heq_of_eq (Functor.comp_map (AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ))
        (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom) f)).trans
        (Functor.map_heq_bridge (AlgebraicGeometry.Scheme.Modules.pushforward
          (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom)
          ((S.veronese m).toGradedAffineAlgebra.twistTransition 1 (leOfHom f.unop))
          ((AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ)).map f) rfl rfl HEq.rfl))
      HEq.rfl HEq.rfl HEq.rfl)⟩

/-- `O_{Proj_X S}(m) ≅ ψ.inv^* O_{Proj_X S^(m)}(1)` where `ψ.inv = (veroneseIso S m hm).inv.left`. Assembly of the
route in the module docstring: `twist = lim twistDiagram` on both sides, `HasLimit.isoOfNatIso` of the leaf
`twistDiagram_iso_nonempty`, `preservesLimitIso` for the right adjoint `(ψ.hom)_*`, and
`pullbackIsoPushforwardInv`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.veronese_twist_pullback_iso
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (m : ℕ) (hm : 0 < m) :
    Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.relativeProj.veroneseIso S m hm).inv.left).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist (S.veronese m) (1 : ℤ))) := by
  obtain ⟨w⟩ := AlgebraicGeometry.Scheme.relativeProj.veroneseIso.twistDiagram_iso_nonempty S m hm
  refine ⟨?_⟩
  -- Instances must be stated in the Scheme-level categories (see the module docstring).
  have hL1 : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ
      (AlgebraicGeometry.Scheme.relativeProj S).left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  have hL2 : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ
      (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  have hinv : (AlgebraicGeometry.Scheme.relativeProj.veroneseIso S m hm).inv.left =
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).inv := rfl
  rw [AlgebraicGeometry.Scheme.relativeProj.twist_eq_limit_twistDiagram S (m : ℤ),
    AlgebraicGeometry.Scheme.relativeProj.twist_eq_limit_twistDiagram (S.veronese m) (1 : ℤ), hinv]
  exact (HasLimit.isoOfNatIso w).symm ≪≫
    (preservesLimitIso (AlgebraicGeometry.Scheme.Modules.pushforward
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).hom)
      (AlgebraicGeometry.Scheme.relativeProj.twistDiagram (S.veronese m) (1 : ℤ))).symm ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforwardInv
      (AlgebraicGeometry.Scheme.relativeProj.veroneseIso.leftIso S m hm).symm).app _).symm

end
