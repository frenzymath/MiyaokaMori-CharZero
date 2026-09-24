import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameSymPower
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFrameCoefficient
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TautologicalSection
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualEvSections
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion

/-! # The tautological section in a frame: `ξ|_{p⁻¹V} = σ(ε^∨) · p^*ε`

Statement: for a frame `ε` of `L` on an open `V ⊆ C` there is a frame `t` of `L^∨` on `V` (the dual frame,
`t(ε) = 1`) such that the tautological section `ξ ∈ Γ(Tot(L), p^*L)` restricted to `p⁻¹V` is
`x • p^*ε`, `x := totalSpace.frameCoordinate L V t = u_1(t ⊗ 1)` ("`σ(t)`"). This fact is shared with
`FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquiv`; the route
formalized is recorded in the docstring of the theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism of sheaves of modules commutes with restriction (element form; private copy). -/
private theorem app_res_tf {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- The compatible family of local functionals `m ↦ coord_ε(m)` attached to a frame `ε` of `M` on `V`
(an element of the authors' local dual `LocalDualSections X M V`). -/
def IsFrame.localDual {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε) :
    Frame.LH M V :=
  ⟨fun W => (hε.coordEquiv (leOfHom W.hom)).toLinearMap, fun W W' i x => by
    have h := hε.coord_map (leOfHom i.left) (leOfHom W'.hom) x
    have hi : i.left = homOfLE (leOfHom i.left) := Subsingleton.elim _ _
    rw [hi]
    exact h⟩

theorem IsFrame.localDual_apply {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε)
    (W : CategoryTheory.Over V) (x : Γ(M, W.left)) :
    hε.localDual.1 W x = hε.coord (leOfHom W.hom) x := rfl

/-- The dual frame `ε^∨ := dualUnit (coord_ε) ∈ Γ(V, M^∨)`. -/
def IsFrame.dualFrameSection {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε) :
    Γ(AlgebraicGeometry.Scheme.Modules.dual M, V) :=
  Frame.dualUnit M V hε.localDual

/-- **The pairing of the dual frame with the frame is `1`**, on every `W' ≤ V`:
`ev(ε^∨|_{W'} ⊗ ε|_{W'}) = 1` (`dualUnit_res`, `dualEv_app_tensorSections_dualUnit`, `coord_frame`). -/
theorem IsFrame.dualEv_dualFrameSection {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε)
    {W' : X.Opens} (h : W' ≤ V) :
    (show Γ(X, W') from (dualEv M).app W'
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual M) M W'
        ((AlgebraicGeometry.Scheme.Modules.dual M).res h hε.dualFrameSection) (M.res h ε))) = 1 := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.dual M).res h hε.dualFrameSection =
      Frame.dualUnit M W' (AlgebraicGeometry.Scheme.Modules.localDualRestrict M (homOfLE h) hε.localDual) :=
    Frame.dualUnit_res M (homOfLE h) hε.localDual
  rw [h1]
  refine (DualZigzag.dualEv_app_tensorSections_dualUnit M W' _ (M.res h ε)).trans ?_
  exact hε.coord_frame h

/-- **The dual frame is a frame of `M^∨`** (`M` a line bundle): locally `ε^∨ = f • g` for a frame `g` of `M^∨`,
and `f · ev(g ⊗ ε) = ev(ε^∨ ⊗ ε) = 1`, so `f` is a unit (`IsFrame.of_isUnit_coord`); glue (`IsFrame.of_iSup`). -/
theorem IsFrame.dualFrameSection_isFrame {M : X.Modules} [M.IsLineBundle] {V : X.Opens} {ε : Γ(M, V)}
    (hε : IsFrame M V ε) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.dual M) V hε.dualFrameSection := by
  let D := AlgebraicGeometry.Scheme.Modules.dual M
  have hD : D.IsLineBundle := moduleSheafDual_isLineBundle M
  let t : Γ(D, V) := hε.dualFrameSection
  have key : ∀ x : X, x ∈ V → ∃ V' : X.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ IsFrame D V' (D.res hV' t) := by
    intro x hx
    obtain ⟨W₁, hxW₁, g, hg⟩ := exists_frame D x
    have h₂V : V ⊓ W₁ ≤ V := inf_le_left
    have h₂₁ : V ⊓ W₁ ≤ W₁ := inf_le_right
    refine ⟨V ⊓ W₁, h₂V, ⟨hx, hxW₁⟩, ?_⟩
    have hg₂ : IsFrame D (V ⊓ W₁) (D.res h₂₁ g) := hg.restrict h₂₁
    let f : Γ(X, V ⊓ W₁) := hg₂.coord le_rfl (D.res h₂V t)
    have hft : D.res h₂V t = f • D.res h₂₁ g := by
      have := hg₂.coord_smul_frame le_rfl (D.res h₂V t)
      rw [res_self] at this
      exact this.symm
    have hpair := hε.dualEv_dualFrameSection h₂V
    let z : Γ(D ⊗ M, V ⊓ W₁) := AlgebraicGeometry.Scheme.Modules.tensorSections D M (V ⊓ W₁) (D.res h₂₁ g) (M.res h₂V ε)
    have h2 : AlgebraicGeometry.Scheme.Modules.tensorSections D M (V ⊓ W₁) (D.res h₂V t) (M.res h₂V ε) = f • z := by
      rw [hft]
      exact tensorSections_smul_left D M (V ⊓ W₁) f (D.res h₂₁ g) (M.res h₂V ε) z rfl
    have h3 : (show Γ(X, V ⊓ W₁) from (dualEv M).app (V ⊓ W₁) (f • z)) =
        f * (show Γ(X, V ⊓ W₁) from (dualEv M).app (V ⊓ W₁) z) :=
      Hom.app_smul (dualEv M) f z
    have hu : IsUnit f := by
      refine IsUnit.of_mul_eq_one _ (h3.symm.trans ?_)
      rw [← h2]
      exact hpair
    exact IsFrame.of_isUnit_coord hg₂ hu
  choose! V' hV' hxV' hfr using key
  refine IsFrame.of_iSup (ι := (V : Set X)) (fun q => V' q.1) (fun q => hV' q.1 q.2) ?_ ?_
  · intro q hq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hxV' q hq⟩
  · intro q
    exact hfr q.1 q.2

/-- Right whiskering on a pure tensor (private copy). -/
private theorem whiskerRight_app_tensorSections_tf {A A' : X.Modules} (f : A ⟶ A') (B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) = AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact tensorHom_tensorSections f (𝟙 B) U a b

/-- The second zigzag identity on a section: `tail2(coev ⊗ v) = v` (`DualZigzag.zigzag2`, element form). -/
private theorem zigzag2_app (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] (V : X.Opens) (v : Γ(M, V)) :
    (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V ((λ_ M).inv.app V v)) = v := by
  have hZ := DualZigzag.zigzag2 M
  unfold CategoryTheory.MonoidalCategory.Zigzag.Z2 at hZ
  have h0 := congrArg (fun φ => Modules.Hom.app φ V) hZ
  have h1 := ConcreteCategory.congr_hom h0 v
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app, ConcreteCategory.id_apply] at h1
  simp only [DualZigzag.tail2, Hom.comp_app, ConcreteCategory.comp_apply]
  exact h1

/-- **The coevaluation in a frame**: `coev|_V = ε^∨ ⊗ ε`. Proof: `ε^∨ ⊗ ε` is a frame of `M^∨ ⊗ M` on `V`
(`IsFrame.moduleTensorSection`), so `coev|_V = c • (ε^∨ ⊗ ε)`; the second zigzag identity `Z2` on the section `ε`
(`DualZigzag.zigzag2`, `tail2_app`) gives `c • ε = ε`, hence `c = 1` (`ε` is a frame). -/
theorem IsFrame.res_coevSection {M : X.Modules} [M.IsLineBundle] {V : X.Opens} {ε : Γ(M, V)}
    (hε : IsFrame M V ε) :
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤)
        (coevSection M) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection hε.dualFrameSection ε := by
  have hD : (AlgebraicGeometry.Scheme.Modules.dual M).IsLineBundle := moduleSheafDual_isLineBundle M
  let t : Γ((AlgebraicGeometry.Scheme.Modules.dual M), V) := hε.dualFrameSection
  have hfrT : IsFrame (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M) V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) :=
    hε.dualFrameSection_isFrame.moduleTensorSection hε
  let c : Γ(X, V) := hfrT.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_top (coevSection M))
  have hc : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤) (coevSection M) = c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε := by
    have h1 := hfrT.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_top (coevSection M))
    have h0 : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_rfl (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) = AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε := res_self (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M) _
    exact h1.symm.trans (congrArg (fun z => c • z) h0)
  -- the zigzag identity `Z2` on `ε`
  have hZε : (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V ((λ_ M).inv.app V ε)) = ε :=
    zigzag2_app M V ε
  have e1 : (λ_ M).inv.app V ε = AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) M V (DualZigzag.unitOne V) ε :=
    DualZigzag.leftUnitor_inv_app M V ε
  have e2 : (DualZigzag.coevHom M ▷ M).app V (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) M V (DualZigzag.unitOne V) ε) =
      AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V ((DualZigzag.coevHom M).app V (DualZigzag.unitOne V)) ε :=
    whiskerRight_app_tensorSections_tf (DualZigzag.coevHom M) M V _ ε
  let z1 : Γ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M, V) := AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual M) M V t ε
  have e3 : (DualZigzag.coevHom M).app V (DualZigzag.unitOne V) = c • z1 := by
    refine (DualZigzag.coevHom_app_one M V).trans ?_
    have h1 : (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom.app V ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤) (coevSection M)) =
        (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom.app V (c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) := congrArg _ hc
    refine h1.trans ?_
    exact Hom.app_smul (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom c (show Γ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M), V) from AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε)
  let w : Γ(((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) ⊗ M, V) := AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V z1 ε
  have e4 : AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V (c • z1) ε = c • w :=
    tensorSections_smul_left ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V c z1 ε w rfl
  have hc1' : hε.localDual.1 (Frame.topZ V) ε = 1 := by
    have h := hε.coord_frame (le_refl V)
    rw [res_self] at h
    exact h
  have e5 : (DualZigzag.tail2 M).app V w = (1 : Γ(X, V)) • ε := by
    refine (DualZigzag.tail2_app M V hε.localDual ε ε).trans ?_
    exact congrArg (fun r : Γ(X, V) => r • ε) hc1'
  have hcε : c • ε = ε := by
    have a1 := congrArg (fun z => (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V z)) e1
    have a2 := congrArg (fun z => (DualZigzag.tail2 M).app V z) e2
    have a3 := congrArg (fun z => (DualZigzag.tail2 M).app V
      (AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V z ε)) e3
    have a4 := congrArg (fun z => (DualZigzag.tail2 M).app V z) e4
    have a5 : (DualZigzag.tail2 M).app V (c • w) = c • (DualZigzag.tail2 M).app V w :=
      Hom.app_smul (DualZigzag.tail2 M) c w
    have a6 := congrArg (fun z : Γ(M, V) => c • z) e5
    have h := a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6))))
    rw [one_smul] at h
    exact h.symm.trans hZε
  -- `c • ε = ε` ⇒ `c = 1`
  have hc1 : c = 1 := by
    refine (hε V le_rfl).1 ?_
    show c • M.res le_rfl ε = (1 : Γ(X, V)) • M.res le_rfl ε
    rw [res_self, one_smul]
    exact hcε
  rw [hc, hc1, one_smul]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **`Θ_1(t ⊗ 1) = symGen t`**: both are `π_1(1 ⊗ t)` (in the quasi-coherent branch of `symGradedAlgebra`;
the `dite` casts are removed by generalizing `symGradedAlgebra (dual L)`). -/
theorem totalSpace.tensorPowerToSymPart_one_app (L : X.Modules) [L.IsLineBundle] [(Modules.dual L).IsLineBundle]
    (V : X.Opens) (t : Γ(Modules.dual L, V)) :
    (totalSpace.tensorPowerToSymPart L 1).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1) =
      (Modules.symGen (Modules.dual L)).app V t := by
  have hq : (Modules.dual L).IsQuasicoherent := inferInstance
  have hS := Modules.symGradedAlgebra_eq_ofQC_of_isLineBundle (Modules.dual L)
  rw [Modules.symGen_eq_of_isQuasicoherent (Modules.dual L) hq]
  unfold totalSpace.tensorPowerToSymPart
  generalize_proofs pf1 pf2 pf3 pf4 pf5
  change (Modules.Hom.app ((Modules.monoidalPowIsoTensorPower (Modules.dual L) 1).inv ≫
      (pf4 pf3).mpr (Modules.symPowπ (Modules.dual L) 1)) V) (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1) =
    (Modules.Hom.app ((λ_ (Modules.dual L)).inv ≫ Modules.symPowπ (Modules.dual L) 1 ≫ eqToHom pf5) V) t
  generalize Modules.symGradedAlgebra (Modules.dual L) = S at hS pf4 pf5 ⊢
  subst hS
  change (Modules.symPowπ (Modules.dual L) 1).app V
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) 1).inv.app V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1)) =
    (Modules.symPowπ (Modules.dual L) 1).app V ((λ_ (Modules.dual L)).inv.app V t)
  rw [Modules.monoidalPowIsoTensorPower_one_inv_app, Modules.DualZigzag.leftUnitor_inv_app]
  rfl

end AlgebraicGeometry.Scheme

/-- (§3 of the paper) **The tautological section in a frame: `ξ|_{p⁻¹V} = σ(t) · p^*ε`, `t = ε^∨`.**

Setting: `L` a line bundle on the smooth projective curve `C`, `p : Tot(L) → C`, `V ⊆ C` open, `ε ∈ Γ(V, L)` a frame
(`IsFrame`), `ξ := tautologicalSection L ∈ Γ(Tot(L), p^*L)`, `x t := totalSpace.frameCoordinate L V t = u_1(t ⊗ 1)`
with `u_1 = Θ_1 ≫ ι_1 ≫ σ : L^∨ ⊗ O → Sym^1 L^∨ → Sym L^∨ → p_*O_Tot`.
Claim: there is a frame `t` of `L^∨` on `V` with `ξ|_{p⁻¹V} = x t • p^*ε` in `Γ(p⁻¹V, p^*L)`
(`p^*ε := unit.app V ε`).

Proof:
1. The dual frame `t := ε^∨ = dualUnit(coord_ε)` (`IsFrame.dualFrameSection`); `ev(t ⊗ ε) = 1` on every `W' ≤ V`
   (`IsFrame.dualEv_dualFrameSection`); `t` is a frame of `L^∨` (`IsFrame.dualFrameSection_isFrame`).
2. `coev|_V = t ⊗ ε` (`IsFrame.res_coevSection`: `t ⊗ ε` is a frame of `L^∨ ⊗ L`, and the zigzag identity `Z2` on `ε`
   forces the coordinate of `coev|_V` to be `1`).
3. `ξ = Ψ(p^*coev)` with `Ψ := p^*(tensorIso) ≫ δ ≫ (ψ ▷ p^*L) ≫ λ`, `ψ := homEquiv⁻¹(symGen ≫ ι_1 ≫ σ)` — this is the
   definition of `tautologicalSection` (`totalSpaceHomEquiv`, `toSection`; the algebra map of `𝟙` is `σ`), `rfl`.
4. Restriction to `p⁻¹V` (`app_res`, `unit_app_map`) and the pure-tensor computation
   (`unit_naturality_app`, `pullbackTensorObjHom_app_unit_tensorSections`, whiskering, `leftUnitor_app_tensorSections`):
   `ξ|_{p⁻¹V} = ψ(p^*t) • p^*ε`.
5. `ψ(p^*t) = (symGen ≫ ι_1 ≫ σ)(t)` (`Adjunction.homEquiv_unit`) `= (Θ_1 ≫ ι_1 ≫ σ)(t ⊗ 1) = x t`
   (`tensorPowerToSymPart_one_app`: `symGen t = Θ_1(t ⊗ 1)`, both `Φ_1⁻¹(1 ⊗ t)`). ∎ -/
theorem exists_dualFrame_tautologicalSection_res {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (V : C.toScheme.Opens) {ε : Γ(L.toModules, V)}
    (hε : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules V ε) :
    ∃ t : Γ(AlgebraicGeometry.Scheme.Modules.dual L.toModules, V),
      AlgebraicGeometry.Scheme.Modules.IsFrame (AlgebraicGeometry.Scheme.Modules.dual L.toModules) V t ∧
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          L.toModules).res (le_top : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤ ⊤)
          (tautologicalSection L) =
        AlgebraicGeometry.Scheme.totalSpace.frameCoordinate L.toModules V t •
          (show Γ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj L.toModules,
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
            ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).unit.app L.toModules).app V ε) := by
  let LM : C.toScheme.Modules := L.toModules
  let D := AlgebraicGeometry.Scheme.Modules.dual LM
  have hD : (AlgebraicGeometry.Scheme.Modules.dual LM).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.moduleSheafDual_isLineBundle LM
  let Tot := AlgebraicGeometry.Scheme.totalSpace LM
  let p := Tot.hom
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra D
  let σ := AlgebraicGeometry.Scheme.relativeSpec.structureHom S.total
  let ψ : (AlgebraicGeometry.Scheme.Modules.pullback p).obj D ⟶ 𝟙_ Tot.left.Modules :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.symGen D ≫ CategoryTheory.Limits.Sigma.ι S.part 1 ≫
        AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total Tot (𝟙 Tot))
  let PL := (AlgebraicGeometry.Scheme.Modules.pullback p).obj LM
  let δ := AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom p D LM
  let Ψ : (AlgebraicGeometry.Scheme.Modules.pullback p).obj (AlgebraicGeometry.Scheme.Modules.tensor D LM) ⟶ PL :=
    (AlgebraicGeometry.Scheme.Modules.pullback p).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D LM).hom ≫
      δ ≫ (ψ ▷ PL) ≫ (λ_ PL).hom
  have hξ : tautologicalSection L =
      Ψ.app ⊤ (sectionPullbackAlong p (AlgebraicGeometry.Scheme.Modules.coevSection LM)) := rfl
  refine ⟨hε.dualFrameSection, hε.dualFrameSection_isFrame, ?_⟩
  let t : Γ(D, V) := hε.dualFrameSection
  let uT := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
    (AlgebraicGeometry.Scheme.Modules.tensor D LM)
  let uD := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app D
  let uL := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app LM
  -- restriction of `ξ` to `p⁻¹V`
  have hres : PL.res (le_top : p ⁻¹ᵁ V ≤ ⊤) (tautologicalSection L) =
      Ψ.app (p ⁻¹ᵁ V) (uT.app V ((AlgebraicGeometry.Scheme.Modules.tensor D LM).res (le_top : V ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.coevSection LM))) := by
    have r1 : PL.res (le_top : p ⁻¹ᵁ V ≤ ⊤) (tautologicalSection L) =
        PL.res (le_top : p ⁻¹ᵁ V ≤ ⊤) (Ψ.app ⊤ (sectionPullbackAlong p (AlgebraicGeometry.Scheme.Modules.coevSection LM))) :=
      congrArg (PL.res le_top) hξ
    have r2 := (AlgebraicGeometry.Scheme.Modules.app_res_tf Ψ (le_top : p ⁻¹ᵁ V ≤ ⊤)
      (sectionPullbackAlong p (AlgebraicGeometry.Scheme.Modules.coevSection LM))).symm
    have r3 := AlgebraicGeometry.Scheme.Modules.unit_app_map p (AlgebraicGeometry.Scheme.Modules.tensor D LM)
      (le_top : V ≤ ⊤) (AlgebraicGeometry.Scheme.Modules.coevSection LM)
    exact r1.trans (r2.trans (congrArg (Ψ.app (p ⁻¹ᵁ V)) r3.symm))
  have hcoev := hε.res_coevSection
  have hΨ : ∀ z, Ψ.app (p ⁻¹ᵁ V) z = (λ_ PL).hom.app (p ⁻¹ᵁ V) ((ψ ▷ PL).app (p ⁻¹ᵁ V)
      (δ.app (p ⁻¹ᵁ V) (((AlgebraicGeometry.Scheme.Modules.pullback p).map
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D LM).hom).app (p ⁻¹ᵁ V) z))) := fun z => rfl
  -- the pure-tensor computation
  have s1 := AlgebraicGeometry.Scheme.Modules.unit_naturality_app p
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D LM).hom V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε)
  have s1' : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj D LM).hom.app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) =
      AlgebraicGeometry.Scheme.Modules.tensorSections D LM V t ε := rfl
  have s2 := AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections p D LM V t ε
  have s3 := AlgebraicGeometry.Scheme.Modules.whiskerRight_app_tensorSections_tf ψ PL (p ⁻¹ᵁ V)
    (uD.app V t) (uL.app V ε)
  have s4 := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections PL (p ⁻¹ᵁ V)
    (show Γ(Tot.left, p ⁻¹ᵁ V) from ψ.app (p ⁻¹ᵁ V) (uD.app V t)) (uL.app V ε)
  refine hres.trans ?_
  refine (congrArg (fun z => Ψ.app (p ⁻¹ᵁ V) (uT.app V z)) hcoev).trans ?_
  refine (hΨ _).trans ?_
  refine (congrArg (fun z => (λ_ PL).hom.app (p ⁻¹ᵁ V) ((ψ ▷ PL).app (p ⁻¹ᵁ V) (δ.app (p ⁻¹ᵁ V) z))) s1).trans ?_
  refine (congrArg (fun z => (λ_ PL).hom.app (p ⁻¹ᵁ V) ((ψ ▷ PL).app (p ⁻¹ᵁ V) (δ.app (p ⁻¹ᵁ V)
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).unit.app (D ⊗ LM)).app V z)))) s1').trans ?_
  refine (congrArg (fun z => (λ_ PL).hom.app (p ⁻¹ᵁ V) ((ψ ▷ PL).app (p ⁻¹ᵁ V) z)) s2).trans ?_
  refine (congrArg (fun z => (λ_ PL).hom.app (p ⁻¹ᵁ V) z) s3).trans ?_
  refine s4.trans ?_
  -- `ψ(p^*t) = x`
  refine congrArg (fun r : Γ(Tot.left, p ⁻¹ᵁ V) => r • (show Γ(PL, p ⁻¹ᵁ V) from uL.app V ε)) ?_
  have hg : (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ ψ =
      AlgebraicGeometry.Scheme.Modules.symGen D ≫ CategoryTheory.Limits.Sigma.ι S.part 1 ≫
        AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total Tot (𝟙 Tot) :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_unit] at hg
  have hg' := congrArg (fun φ => φ.app V t) hg
  change ψ.app (p ⁻¹ᵁ V) (uD.app V t) =
    σ.app V ((CategoryTheory.Limits.Sigma.ι S.part 1).app V ((AlgebraicGeometry.Scheme.Modules.symGen D).app V t)) at hg'
  refine hg'.trans ?_
  change σ.app V ((CategoryTheory.Limits.Sigma.ι S.part 1).app V ((AlgebraicGeometry.Scheme.Modules.symGen D).app V t)) =
    σ.app V ((CategoryTheory.Limits.Sigma.ι S.part 1).app V
      ((AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart LM 1).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1)))
  rw [AlgebraicGeometry.Scheme.totalSpace.tensorPowerToSymPart_one_app LM V t]

end
