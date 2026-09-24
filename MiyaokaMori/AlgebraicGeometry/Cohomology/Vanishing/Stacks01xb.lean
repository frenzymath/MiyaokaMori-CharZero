import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01x9
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01ew

/-! # Serre's affine vanishing (Stacks 01XB)

Higher cohomology of a quasi-coherent sheaf on an affine open vanishes (Stacks 01XB, Serre's affine
vanishing): for `U ⊆ X` an affine open and `F` quasi-coherent, `H^p(U, F) = 0` for `p > 0`.

Proof: apply Cartan's criterion (Stacks 01EW) with `B` = the affine opens and `Cov V` = the standard
(finite) open covers `{D(f_i)}` of `V` (`f_i ∈ Γ(X, V)`, `⨆ D(f_i) = V`):
(1) nonempty finite intersections of a standard cover, `⨅_{i ∈ s} D(f_i) = D(∏_{i ∈ s} f_i)`, are affine
    opens;
(2) cofinality: every open cover `{W_j}` of `V` is refined by a standard cover — at each point choose
    `D(f) ⊆` some `W_j` (`IsAffineOpen.exists_basicOpen_le`); these `f` generate the unit ideal
    (`IsAffineOpen.self_le_iSup_basicOpen_iff`); a finite subset (`Ideal.span_eq_top_iff_finite`) gives a
    finite standard cover;
(3) Čech acyclicity on standard covers is Stacks 01X9.

Source: Stacks 01XB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01xbAux

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The standard open covers of `V`: finite families `D(f_0), …, D(f_{n-1})` (`f_i ∈ Γ(X, V)`) covering `V`. -/
def stdCov (V : X.Opens) : Set (Σ n : ℕ, Fin n → X.Opens) :=
  {c | ∃ f : Fin c.1 → Γ(X, V), (∀ i, c.2 i = X.basicOpen (f i)) ∧ ⨆ i, X.basicOpen (f i) = V}

/-- A nonempty finite intersection of a standard cover is a basic open, hence an affine open. -/
theorem biInf_basicOpen_mem_affineOpens {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    (f : Fin n → Γ(X, V)) (s : Finset (Fin n)) (hs : s.Nonempty) :
    (⨅ i ∈ s, X.basicOpen (f i)) ∈ X.affineOpens := by
  have h1 : (⨅ i ∈ s, X.basicOpen (f i)) = X.basicOpen (∏ i ∈ s, f i) := by
    rw [Stacks01x9Aux.basicOpen_finset_prod s f, Finset.inf_eq_iInf]
    obtain ⟨i, hi⟩ := hs
    refine (inf_eq_right.2 ?_).symm
    exact (iInf₂_le i hi).trans (X.basicOpen_le _)
  rw [h1]
  exact hV.basicOpen _

/-- Every open cover of an affine open `V` is refined by some standard open cover. -/
theorem exists_stdCov_refines {V : X.Opens} (hV : IsAffineOpen V) (ι : Type u) (W : ι → X.Opens)
    (hW : ⨆ j, W j = V) :
    ∃ c ∈ stdCov V, ∀ i, ∃ j, c.2 i ≤ W j := by
  classical
  -- for each point `x ∈ V` choose a basic open `D(f x)` containing `x` and contained in some `W j`
  have key : ∀ x : V, ∃ g : Γ(X, V), (∃ j, X.basicOpen g ≤ W j) ∧ (x : X) ∈ X.basicOpen g := by
    intro x
    have hx : (x : X) ∈ (⨆ j, W j : X.Opens) := by rw [hW]; exact x.2
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basicOpen_le (V := W j) ⟨x, hj⟩ x.2
    exact ⟨g, ⟨j, hg₁⟩, hg₂⟩
  choose f hf₁ hf₂ using key
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    rw [iSup_range', Opens.mem_iSup]
    exact ⟨_, hf₂ ⟨x, hx⟩⟩
  obtain ⟨t, ht₁, ht₂⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  -- arrange `t` as a finite family
  let e := Fintype.equivFin {x : Γ(X, V) // x ∈ t}
  set n := Fintype.card {x : Γ(X, V) // x ∈ t} with hn
  let g : Fin n → Γ(X, V) := fun i => (e.symm i : Γ(X, V))
  have hgt : ∀ i, g i ∈ t := fun i => (e.symm i).2
  have hcover : ⨆ i, X.basicOpen (g i) = V := by
    refine le_antisymm (iSup_le fun i => X.basicOpen_le _) ?_
    rw [← hV.self_le_iSup_basicOpen_iff] at ht₂
    refine ht₂.trans (iSup_le ?_)
    rintro ⟨x, hx⟩
    have hx' : g (e ⟨x, hx⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
    calc X.basicOpen x = X.basicOpen (g (e ⟨x, hx⟩)) := by rw [hx']
      _ ≤ ⨆ i, X.basicOpen (g i) := le_iSup (fun i => X.basicOpen (g i)) (e ⟨x, hx⟩)
  refine ⟨⟨n, fun i => X.basicOpen (g i)⟩, ⟨g, fun i => rfl, hcover⟩, ?_⟩
  intro i
  obtain ⟨x, hx⟩ := ht₁ (hgt i)
  obtain ⟨j, hj⟩ := hf₁ x
  refine ⟨j, ?_⟩
  show X.basicOpen (g i) ≤ W j
  rw [← hx]
  exact hj

end Stacks01xbAux

theorem sheafCohomology'_affineOpen_vanishing {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (M.toAddCommGrpSheaf.H' p U) := by
  refine sheafCohomology'_vanishing_of_cech_basis M X.affineOpens X.isBasis_affineOpens
    Stacks01xbAux.stdCov ?_ ?_ ?_ U hU p hp
  · -- (1) the covers and their nonempty finite intersections lie in `B`
    intro V hV c hc
    obtain ⟨f, hcf, hsup⟩ := hc
    have hc2 : c.2 = fun i => X.basicOpen (f i) := funext hcf
    rw [hc2]
    exact ⟨hsup, fun s hs => Stacks01xbAux.biInf_basicOpen_mem_affineOpens hV f s hs⟩
  · -- (2) cofinality
    exact fun V hV ι W hW => Stacks01xbAux.exists_stdCov_refines hV ι W hW
  · -- (3) Čech acyclicity on standard covers (Stacks 01X9)
    intro V hV c hc q hq
    obtain ⟨f, hcf, hsup⟩ := hc
    have hc2 : c.2 = fun i => X.basicOpen (f i) := funext hcf
    rw [hc2]
    exact cechComplexAlt_standardCover_acyclic M hV f hsup q hq

end
