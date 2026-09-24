import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModulesAssociatedPoints
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModuleSupportGenericPoints
import MiyaokaMori.RingTheory.Localization.RegularMeromorphicSectionAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # Sections of a scheme without embedded points are determined by germs at minimal points

Sections of the structure sheaf of a locally Noetherian scheme without embedded points are determined
by their germs at the minimal points (Stacks 0EMI, first sentence; 02OZ), and the bookkeeping around it.

* `IsMinimalPoint y`: `∀ z, z ⤳ y → z = y` (the generic points of the irreducible components of `X`).
* `nontrivial_unit_stalk`, `genericPoints_unit_eq`: `Supp O_X = X`, so the generic points of the
  coherent module `O_X` (`ModuleSupportGenericPoints`) are exactly the minimal points; hence
  `exists_isMinimalPoint_specializes` (every point is a specialization of a minimal point) and
  `finite_isMinimalPoint_inter` (finitely many minimal points in an affine open), for `X` locally Noetherian.
* `isAssociatedPoint_unit_iff`: `x` is an associated point of `O_X` iff `m_x ∈ Ass_{O_{X,x}}(O_{X,x})`
  (the stalk of `O_X` as a module is `O_{X,x}`, `unitStalkLinearEquiv`).
* `primeIdealOf_mem_minimalPrimes_bot_of_isMinimalPoint`: for `y ∈ U` affine minimal, `p_y` is a minimal
  prime of `Γ(U, O_X)` (primes `q ≤ p_y` correspond to generalizations of `y`).
* `isAssociatedPoint_unit_of_isMinimalPoint`: minimal points are associated points
  (`m_y = rad(0) ∈ Ass(O_{X,y})`, `Stacks02ozAlgebra`).
* `section_eq_zero_of_germ_isMinimalPoint_eq_zero` (**the key fact**): `X` locally Noetherian without
  embedded points, `U` affine, `f ∈ Γ(U, O_X)` with `germ_y f = 0` for every minimal point `y ∈ U`; then
  `f = 0`. Proof (Stacks 00LD, 0EMI): if `f ≠ 0`, the Noetherian module `A f` (`A = Γ(U, O_X)`) has an
  associated prime `q = rad(Ann_A(g f))`; the point `z ∈ U` with `p_z = q` is an associated point of `O_X`
  (`m_z = rad(Ann_{O_z}(g f / 1))`, `Stacks02ozAlgebra`); a minimal point `y ⤳ z` is also
  associated, so `z = y` by the no-embedded-points hypothesis, so `z` is minimal and `germ_z f = 0`, i.e.
  `t f = 0` for some `t ∉ q`; but then `t ∈ Ann(g f) ⊆ q`, contradiction.

Source: Stacks 02OZ, 0EMI, 00LD, 05AI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A minimal point (for specialization) of a scheme: a generic point of an irreducible component. -/
def IsMinimalPoint (y : X) : Prop := ∀ z : X, z ⤳ y → z = y

namespace Modules

theorem nontrivial_unit_stalk (x : X) :
    Nontrivial ((unitModule X).presheaf.stalk x) :=
  (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv X x).toEquiv.nontrivial_congr.mpr inferInstance

theorem unit_support_eq_univ :
    (unitModule X).support = Set.univ :=
  Set.eq_univ_of_forall fun x => nontrivial_unit_stalk x

theorem genericPoints_unit_eq :
    (unitModule X).genericPoints = {y | IsMinimalPoint y} := by
  ext y
  simp only [genericPoints, unit_support_eq_univ, Set.mem_univ, true_and, Set.mem_ofPred_eq,
    true_implies]
  rfl

theorem unit_isCoherent [AlgebraicGeometry.IsLocallyNoetherian X] :
    (unitModule X).IsCoherent :=
  isCoherent_of_isLocallyFree _

/-- Every point is a specialization of a minimal point (`X` locally Noetherian). -/
theorem exists_isMinimalPoint_specializes [AlgebraicGeometry.IsLocallyNoetherian X] (x : X) :
    ∃ y : X, IsMinimalPoint y ∧ y ⤳ x := by
  haveI := unit_isCoherent (X := X)
  obtain ⟨y, hy, hyx⟩ := exists_mem_genericPoints_specializes
    (unitModule X) (nontrivial_unit_stalk x)
  rw [genericPoints_unit_eq] at hy
  exact ⟨y, hy, hyx⟩

/-- Finitely many minimal points in an affine open (`X` locally Noetherian). -/
theorem finite_isMinimalPoint_inter [AlgebraicGeometry.IsLocallyNoetherian X] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) : ({y : X | IsMinimalPoint y} ∩ (U : Set X)).Finite := by
  haveI := unit_isCoherent (X := X)
  have := finite_genericPoints_inter (unitModule X) hU
  rwa [genericPoints_unit_eq] at this

/-- Associated points of the structure sheaf, in terms of the local rings. -/
theorem isAssociatedPoint_unit_iff (x : X) :
    IsAssociatedPoint (unitModule X) x ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimes (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.unit X.ringCatSheaf) x
  show IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈ associatedPrimes (X.presheaf.stalk x)
    ((unitModule X).presheaf.stalk x) ↔ _
  rw [LinearEquiv.AssociatedPrimes.eq (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv X x)]

/-- For `y ∈ U` affine and minimal, `p_y` is a minimal prime of `Γ(U, O_X)`. -/
theorem primeIdealOf_mem_minimalPrimes_bot_of_isMinimalPoint {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {y : X} (hy : y ∈ U) (hmin : IsMinimalPoint y) :
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∈ (⊥ : Ideal Γ(X, U)).minimalPrimes := by
  refine ⟨⟨(hU.primeIdealOf ⟨y, hy⟩).isPrime, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hqp
  let q' : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  let z : X := hU.fromSpec q'
  have hzU : z ∈ U := by
    have : z ∈ Set.range hU.fromSpec.base := ⟨q', rfl⟩
    rwa [hU.range_fromSpec] at this
  have hqz : hU.primeIdealOf ⟨z, hzU⟩ = q' := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hzy : z ⤳ y := by
    have h1 : q' ⤳ hU.primeIdealOf ⟨y, hy⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hqp
    have h2 := h1.map hU.fromSpec.base.hom.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hy⟩] at h2
  have hzy' : z = y := hmin z hzy
  have : q' = hU.primeIdealOf ⟨y, hy⟩ := by
    rw [← hqz]
    congr 1
    exact Subtype.ext hzy'
  rw [show q = q'.asIdeal from rfl, this]

/-- Minimal points are associated points of the structure sheaf. -/
theorem isAssociatedPoint_unit_of_isMinimalPoint {y : X} (hmin : IsMinimalPoint y) :
    IsAssociatedPoint (unitModule X) y := by
  obtain ⟨U, hU, hyU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show y ∈ (⊤ : X.Opens) from trivial)
  have hU : AlgebraicGeometry.IsAffineOpen U := hU
  rw [isAssociatedPoint_unit_iff]
  letI := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  exact IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_mem_minimalPrimes
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal (primeIdealOf_mem_minimalPrimes_bot_of_isMinimalPoint hU hyU hmin)

/-- **Key fact** (Stacks 0EMI / 00LD): on a locally Noetherian scheme without embedded points, a section
of `O_X` over an affine open whose germs vanish at all minimal points is zero. -/
theorem section_eq_zero_of_germ_isMinimalPoint_eq_zero [AlgebraicGeometry.IsLocallyNoetherian X]
    (hX : X.HasNoEmbeddedPoints) {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (f : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), IsMinimalPoint y → X.presheaf.germ U y hy f = 0) : f = 0 := by
  by_contra hf
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  -- the cyclic module `A f` has an associated prime `q = rad(Ann(g f))`
  let M := Submodule.span Γ(X, U) ({f} : Set Γ(X, U))
  haveI : Nontrivial M := by
    refine ⟨⟨⟨f, Submodule.mem_span_singleton_self f⟩, 0, fun h0 => hf ?_⟩⟩
    exact congrArg Subtype.val h0
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty Γ(X, U) M
  obtain ⟨hqprime, m, hm⟩ := hq
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp m.2
  have hcolon : (⊥ : Submodule Γ(X, U) M).colon {m} = (⊥ : Submodule Γ(X, U) Γ(X, U)).colon {m.1} := by
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot,
      Submodule.mem_bot]
    constructor
    · intro h0
      exact congrArg Subtype.val h0
    · intro h0
      exact Subtype.ext h0
  rw [hcolon] at hm
  let q' : PrimeSpectrum Γ(X, U) := ⟨q, hqprime⟩
  let z : X := hU.fromSpec q'
  have hzU : z ∈ U := by
    have : z ∈ Set.range hU.fromSpec.base := ⟨q', rfl⟩
    rwa [hU.range_fromSpec] at this
  have hqz : hU.primeIdealOf ⟨z, hzU⟩ = q' := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  set p := hU.primeIdealOf ⟨z, hzU⟩ with hpdef
  have hpq : p.asIdeal = q := congrArg PrimeSpectrum.asIdeal hqz
  have hm' : p.asIdeal = ((⊥ : Submodule Γ(X, U) Γ(X, U)).colon {m.1}).radical := by
    rw [hpq]
    exact hm
  letI := X.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk z) p.asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩
  -- `z` is an associated point of `O_X`
  have hzass : IsAssociatedPoint (unitModule X) z := by
    rw [isAssociatedPoint_unit_iff]
    exact IsLocalization.AtPrime.maximalIdeal_mem_associatedPrimes_of_eq_radical p.asIdeal m.1 hm'
  -- a minimal point `y ⤳ z` is associated too, so `z = y` is minimal
  obtain ⟨y, hymin, hyz⟩ := exists_isMinimalPoint_specializes z
  have hyass := isAssociatedPoint_unit_of_isMinimalPoint hymin
  have hyz' : y = z := hX y z hyass hzass hyz
  have hzmin : IsMinimalPoint z := hyz' ▸ hymin
  -- so the germ of `f` at `z` vanishes: `t * f = 0` with `t ∉ q`
  have h0 : algebraMap Γ(X, U) (X.presheaf.stalk z) f = 0 := h z hzU hzmin
  rw [IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl] at h0
  obtain ⟨t, ht⟩ := h0
  have h1 : (t : Γ(X, U)) ∈ ((⊥ : Submodule Γ(X, U) Γ(X, U)).colon {m.1}).radical := by
    apply Ideal.le_radical
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul, ← hg, smul_eq_mul,
      mul_left_comm, ht, mul_zero]
  rw [← hm'] at h1
  exact t.2 h1

end Modules

end AlgebraicGeometry.Scheme

end
