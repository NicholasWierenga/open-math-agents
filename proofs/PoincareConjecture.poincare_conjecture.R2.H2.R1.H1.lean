import OMAReductions.R_PoincareConjecture_poincare_conjecture_R2_H2_R1
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Bases
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Universal covering construction adapted from DifferentialGeometry v0.1.3
by Ziyang Qin, Yuan Liao, Ayush Khaitan, Bennett Chow and contributors,
revision 7a48598d35109aa99d1cc678e2724c213cdf4ff3, Apache-2.0.
The original modules are combined into one file and the finite-fiber corollary
for Euclidean three-manifolds is added at the end.
-/

/- Source module: SemilocallySimplyConnected.lean -/


open Set Function Filter Metric Bundle Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology

class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] :
    Prop where
  out : ∀ x : X, ∃ U ∈ nhds x, ∀ γ : _root_.Path x x,
          Set.range γ.toContinuousMap ⊆ U →
            (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧

theorem contractible_loops_nullhomotopic_in_subset
    {X : Type*} [TopologicalSpace X]
    {U : Set X} [ContractibleSpace U]
    {x : X}
    (γ : _root_.Path x x)
    (hγU : Set.range γ.toContinuousMap ⊆ U) :
    (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
  have hSC : IsSimplyConnected U := (inferInstance : SimplyConnectedSpace U)
  have hmem : ∀ t, γ t ∈ U := by
    intro t
    have ht : γ t ∈ Set.range γ.toContinuousMap := by
      refine ⟨t, ?_⟩
      simp [Path.coe_toContinuousMap]
    exact hγU ht
  obtain ⟨F, _⟩ :=
    (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hSC).2 x γ hmem
  exact Quotient.sound ⟨F⟩

section ChartContractible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

include I in
omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem exists_contractible_open_nhd (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ContractibleSpace U := by
  set e : OpenPartialHomeomorph M E :=
    (chartAt H x).transHomeomorph I.toHomeomorph with he_def
  have he_source : e.source = (chartAt H x).source := rfl
  set c : E := e x with hc_def
  have hxsrc : x ∈ e.source := by
    rw [he_source]; exact mem_chart_source H x
  have hc_target : c ∈ e.target := e.map_source hxsrc
  have h_target_open : IsOpen e.target := e.open_target
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    Metric.isOpen_iff.mp h_target_open c hc_target
  set B : Set E := Metric.ball c r with hB_def
  set U : Set M := e.source ∩ e ⁻¹' B with hU_def
  have hU_open : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    refine ⟨hxsrc, ?_⟩
    change e x ∈ B
    simp [hB_def, ← hc_def, Metric.mem_ball, dist_self, hr_pos]
  have heImage : e '' U = B := by
    ext b
    refine ⟨?_, ?_⟩
    · rintro ⟨m, ⟨_, hmB⟩, rfl⟩
      exact hmB
    · intro hb
      have hbT : b ∈ e.target := hr_sub hb
      refine ⟨e.symm b, ⟨e.map_target hbT, ?_⟩, e.right_inv hbT⟩
      change e (e.symm b) ∈ B
      rw [e.right_inv hbT]
      exact hb
  have hU_sub : U ⊆ e.source := Set.inter_subset_left
  let φ : U ≃ₜ B := e.homeomorphOfImageSubsetSource hU_sub heImage
  have hB_contr : ContractibleSpace B := Metric.contractibleSpace_ball hr_pos
  have hU_contr : ContractibleSpace U := φ.contractibleSpace
  exact ⟨U, hU_open, hxU, hU_contr⟩

include I in
omit [InnerProductSpace ℝ E] [IsManifold I ∞ M] in
theorem manifold_semilocallySimplyConnectedSpace :
    SemilocallySimplyConnectedSpace M := ⟨by
  intro x
  obtain ⟨U, hU_open, hxU, hU_contr⟩ := exists_contractible_open_nhd (I := I) x
  refine ⟨U, hU_open.mem_nhds hxU, fun γ hγU => ?_⟩
  exact contractible_loops_nullhomotopic_in_subset γ hγU⟩

end ChartContractible

end Topology
end Riemannian
end Geometry
end DifferentialGeometry

/- Source module: Basic.lean -/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]

def _root_.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
    (X : Type*) [TopologicalSpace X] [Inhabited X] : Type _ :=
  (x : X) × _root_.Path.Homotopic.Quotient (default : X) x

def proj :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X :=
  Sigma.fst

def basicOpen
    (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (U : Set X) :
    Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  { q | ∃ η : _root_.Path p.1 q.1,
          (∀ t, η t ∈ U) ∧
            q.2 =
              (p.2.trans
                ((_root_.Path.Homotopic.Quotient.mk η :
                    _root_.Path.Homotopic.Quotient p.1 q.1))) }

instance topology :
    TopologicalSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
  TopologicalSpace.generateFrom
    { S | ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
            (U : Set X) (_hU : IsOpen U) (_hp : p.1 ∈ U),
              S = basicOpen p U }

theorem basis_trans_shift
    {p q r : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U U' : Set X} (hsub : U' ⊆ U)
    (hqp : q ∈ basicOpen p U)
    (hrq : r ∈ basicOpen q U') :
    r ∈ basicOpen p U := by
  obtain ⟨η, hη, hq2⟩ := hqp
  obtain ⟨η', hη', hr2⟩ := hrq
  refine ⟨η.trans η', ?_, ?_⟩
  · intro t
    have hmem : (η.trans η') t ∈ Set.range η ∪ Set.range η' := by
      have hrng : Set.range (η.trans η') = Set.range η ∪ Set.range η' :=
        Path.trans_range η η'
      have htmem : (η.trans η') t ∈ Set.range (η.trans η') := Set.mem_range_self _
      rw [hrng] at htmem
      exact htmem
    rcases hmem with hin | hin
    · obtain ⟨s, hs⟩ := hin
      exact hs ▸ hη s
    · obtain ⟨s, hs⟩ := hin
      exact hsub (hs ▸ hη' s)
  · have hmk :
        (_root_.Path.Homotopic.Quotient.mk (η.trans η') :
            _root_.Path.Homotopic.Quotient p.1 r.1)
          = (_root_.Path.Homotopic.Quotient.mk η).trans
              (_root_.Path.Homotopic.Quotient.mk η') :=
      _root_.Path.Homotopic.Quotient.mk_trans η η'
    rw [hmk, hr2, hq2]
    exact (_root_.Path.Homotopic.Quotient.trans_assoc p.2
      (_root_.Path.Homotopic.Quotient.mk η)
      (_root_.Path.Homotopic.Quotient.mk η'))

theorem basis_intersection
    [LocallyPathConnectedSpace X]
    {p₁ p₂ r : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U₁ U₂ : Set X} (hU₁ : IsOpen U₁)
    (hU₂ : IsOpen U₂)
    (hr : r ∈ basicOpen p₁ U₁ ∩ basicOpen p₂ U₂) :
    ∃ (V : Set X) (_hV : IsOpen V) (_hrV : r.1 ∈ V),
      V ⊆ U₁ ∩ U₂ ∧ IsPathConnected V ∧
        basicOpen r V ⊆
          basicOpen p₁ U₁ ∩ basicOpen p₂ U₂ := by
  obtain ⟨⟨η₁, hη₁, hr2_1⟩, ⟨η₂, hη₂, hr2_2⟩⟩ := hr
  have hrU₁ : r.1 ∈ U₁ := by
    have h1 := hη₁ 1
    simpa using h1
  have hrU₂ : r.1 ∈ U₂ := by
    have h1 := hη₂ 1
    simpa using h1
  have hrU : r.1 ∈ U₁ ∩ U₂ := ⟨hrU₁, hrU₂⟩
  have hUcap_open : IsOpen (U₁ ∩ U₂) := hU₁.inter hU₂
  obtain ⟨V, ⟨hVopen, hrV, hVpc⟩, hVsub⟩ :=
    (isOpen_isPathConnected_basis r.1).mem_iff.mp (hUcap_open.mem_nhds hrU)
  refine ⟨V, hVopen, hrV, hVsub, hVpc, ?_⟩
  intro s hs
  obtain ⟨ζ, hζ, hs2⟩ := hs
  refine ⟨?_, ?_⟩
  · refine ⟨η₁.trans ζ, ?_, ?_⟩
    · intro t
      have hmem : (η₁.trans ζ) t ∈ Set.range η₁ ∪ Set.range ζ := by
        have hrng : Set.range (η₁.trans ζ) = Set.range η₁ ∪ Set.range ζ :=
          Path.trans_range η₁ ζ
        have htmem : (η₁.trans ζ) t ∈ Set.range (η₁.trans ζ) := Set.mem_range_self _
        rw [hrng] at htmem; exact htmem
      rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hη₁ u
      · exact (hVsub (hu ▸ hζ u)).1
    · have hmk :
          (_root_.Path.Homotopic.Quotient.mk (η₁.trans ζ) :
              _root_.Path.Homotopic.Quotient p₁.1 s.1)
            = (_root_.Path.Homotopic.Quotient.mk η₁).trans
                (_root_.Path.Homotopic.Quotient.mk ζ) :=
        _root_.Path.Homotopic.Quotient.mk_trans η₁ ζ
      rw [hmk, hs2, hr2_1]
      exact (_root_.Path.Homotopic.Quotient.trans_assoc p₁.2
        (_root_.Path.Homotopic.Quotient.mk η₁)
        (_root_.Path.Homotopic.Quotient.mk ζ))
  · refine ⟨η₂.trans ζ, ?_, ?_⟩
    · intro t
      have hmem : (η₂.trans ζ) t ∈ Set.range η₂ ∪ Set.range ζ := by
        have hrng : Set.range (η₂.trans ζ) = Set.range η₂ ∪ Set.range ζ :=
          Path.trans_range η₂ ζ
        have htmem : (η₂.trans ζ) t ∈ Set.range (η₂.trans ζ) := Set.mem_range_self _
        rw [hrng] at htmem; exact htmem
      rcases hmem with ⟨u, hu⟩ | ⟨u, hu⟩
      · exact hu ▸ hη₂ u
      · exact (hVsub (hu ▸ hζ u)).2
    · have hmk :
          (_root_.Path.Homotopic.Quotient.mk (η₂.trans ζ) :
              _root_.Path.Homotopic.Quotient p₂.1 s.1)
            = (_root_.Path.Homotopic.Quotient.mk η₂).trans
                (_root_.Path.Homotopic.Quotient.mk ζ) :=
        _root_.Path.Homotopic.Quotient.mk_trans η₂ ζ
      rw [hmk, hs2, hr2_2]
      exact (_root_.Path.Homotopic.Quotient.trans_assoc p₂.2
        (_root_.Path.Homotopic.Quotient.mk η₂)
        (_root_.Path.Homotopic.Quotient.mk ζ))

theorem basis_covers
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :
    ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
      (U : Set X) (_hU : IsOpen U) (_hp : p.1 ∈ U),
        q ∈ basicOpen p U := by
  refine ⟨q, Set.univ, isOpen_univ, Set.mem_univ _, ?_⟩
  refine ⟨_root_.Path.refl q.1, fun _ => Set.mem_univ _, ?_⟩
  have hmkrefl :
      (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl q.1) :
          _root_.Path.Homotopic.Quotient q.1 q.1)
        = _root_.Path.Homotopic.Quotient.refl q.1 :=
    _root_.Path.Homotopic.Quotient.mk_refl q.1
  rw [hmkrefl]
  exact (_root_.Path.Homotopic.Quotient.trans_refl q.2).symm

theorem basis_assemble
    [LocallyPathConnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis
      { S : Set (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) |
          ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
            (U : Set X) (_hU : IsOpen U) (_hp : p.1 ∈ U),
              S = basicOpen p U } := by
  refine
    { exists_subset_inter := ?_
      sUnion_eq := ?_
      eq_generateFrom := rfl }
  · rintro t₁ ⟨p₁, U₁, hU₁, hp₁, rfl⟩ t₂ ⟨p₂, U₂, hU₂, hp₂, rfl⟩ x hx
    obtain ⟨V, hVopen, hxV, _hVsub, _hVpc, hVin⟩ :=
      basis_intersection (p₁ := p₁) (p₂ := p₂) (r := x)
        hU₁ hU₂ hx
    refine ⟨basicOpen x V, ⟨x, V, hVopen, hxV, rfl⟩, ?_, hVin⟩
    refine ⟨_root_.Path.refl x.1, fun _ => hxV, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x.1) :
            _root_.Path.Homotopic.Quotient x.1 x.1)
          = _root_.Path.Homotopic.Quotient.refl x.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl x.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl x.2).symm
  · apply Set.eq_univ_of_forall
    intro q
    obtain ⟨p, U, hU, hp, hmem⟩ := basis_covers q
    exact ⟨basicOpen p U, ⟨p, U, hU, hp, rfl⟩, hmem⟩

theorem proj_continuous :
    Continuous
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro U hU
  rw [_root_.mem_nhds_iff] at hU
  obtain ⟨W, hWU, hWopen, hqW⟩ := hU
  have hbasic_open : IsOpen (basicOpen q W) :=
    TopologicalSpace.GenerateOpen.basic _ ⟨q, W, hWopen, hqW, rfl⟩
  have hqmem : q ∈ basicOpen q W := by
    refine ⟨_root_.Path.refl q.1, fun _ => hqW, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl q.1) :
            _root_.Path.Homotopic.Quotient q.1 q.1)
          = _root_.Path.Homotopic.Quotient.refl q.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl q.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl q.2).symm
  have hsub : basicOpen q W ⊆ proj ⁻¹' U := by
    intro s hs
    obtain ⟨η, hη, _⟩ := hs
    have hη1 : η 1 ∈ W := hη 1
    have hs1 : s.1 ∈ W := by simpa using hη1
    exact hWU hs1
  exact Filter.mem_of_superset (hbasic_open.mem_nhds hqmem) hsub

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end

/- Source module: CoveringMap.lean -/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

variable {X : Type*} [TopologicalSpace X] [Inhabited X]
  [ConnectedSpace X] [LocallyPathConnectedSpace X]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]

omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_sheet_bijection_on_good_U
    (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (U : Set X) (hp : p.1 ∈ U)
    (hUpc : IsPathConnected U)
    (hUloops : ∀ γ : _root_.Path p.1 p.1,
      (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p.1 p.1) =
          ⟦_root_.Path.refl p.1⟧) :
    Set.BijOn (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      (basicOpen p U) U := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨η, hηU, _⟩ := hq
    have : η 1 ∈ U := hηU 1
    simpa [proj, Path.target] using this
  · intro q hq q' hq' hqq'
    obtain ⟨xq, cq⟩ := q
    obtain ⟨xq', cq'⟩ := q'
    obtain ⟨η, hηU, hqeq⟩ := hq
    obtain ⟨η', hη'U, hq'eq⟩ := hq'
    have hxy : xq = xq' := hqq'
    subst hxy
    refine Sigma.ext rfl ?_
    simp only [heq_eq_eq] at hqeq hq'eq ⊢
    rw [hqeq, hq'eq]
    congr 1
    have hloop_inU : ∀ t, (η.trans η'.symm) t ∈ U := by
      intro t
      rw [Path.trans_apply]
      split_ifs with h
      · exact hηU _
      · rw [Path.symm_apply]; exact hη'U _
    have hloop : (⟦η.trans η'.symm⟧ : Path.Homotopic.Quotient p.1 p.1) =
        ⟦Path.refl p.1⟧ := hUloops _ hloop_inU
    have hbase : Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk η)
        (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')) =
        Path.Homotopic.Quotient.refl p.1 := by
      have h := hloop
      change Path.Homotopic.Quotient.mk (η.trans η'.symm) =
             Path.Homotopic.Quotient.mk (Path.refl p.1) at h
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.mk_refl] at h
      exact h
    have h₁ : Path.Homotopic.Quotient.mk η =
        Path.Homotopic.Quotient.trans
          (Path.Homotopic.Quotient.mk η)
          (Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
            (Path.Homotopic.Quotient.mk η')) := by
      rw [Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
    calc Path.Homotopic.Quotient.mk η
        = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk η)
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η'))
              (Path.Homotopic.Quotient.mk η')) := h₁
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.trans
              (Path.Homotopic.Quotient.mk η)
              (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk η')))
            (Path.Homotopic.Quotient.mk η') := by
            rw [Path.Homotopic.Quotient.trans_assoc]
      _ = Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.refl p.1)
            (Path.Homotopic.Quotient.mk η') := by rw [hbase]
      _ = Path.Homotopic.Quotient.mk η' := by
            rw [Path.Homotopic.Quotient.refl_trans]
  · intro y hy
    have hjoined : JoinedIn U p.1 y := hUpc.joinedIn _ hp _ hy
    refine ⟨⟨y, p.2.trans (Path.Homotopic.Quotient.mk hjoined.somePath)⟩, ?_, rfl⟩
    refine ⟨hjoined.somePath, ?_, rfl⟩
    exact fun t => hjoined.somePath_mem t

omit [Inhabited X] [ConnectedSpace X] in
private theorem uc_good_nhd_exists (x : X) :
    ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧ IsPathConnected U ∧
      ∀ γ : _root_.Path x x, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient x x) = ⟦_root_.Path.refl x⟧ := by
  obtain ⟨U₀, hU₀nhd, hU₀loops⟩ :=
    DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace.out
      (X := X) x
  obtain ⟨U, ⟨hUopen, hxU, hUpc⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp hU₀nhd
  refine ⟨U, hUopen, hxU, hUpc, ?_⟩
  intro γ hγU
  refine hU₀loops γ ?_
  intro y hy
  obtain ⟨t, ht⟩ := hy
  have : γ t ∈ U := by simpa [Path.coe_toContinuousMap] using hγU t
  exact hUsub (ht ▸ this)


omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_disjoint
    {U : Set X}
    {p₁ p₂ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    (hp₁U : p₁.1 ∈ U) (hp₂U : p₂.1 ∈ U)
    (hp_eq : p₁.1 = p₂.1)
    (hUloops : ∀ γ : _root_.Path p₁.1 p₁.1, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p₁.1 p₁.1) =
          ⟦_root_.Path.refl p₁.1⟧)
    (hne : p₁ ≠ p₂) :
    Disjoint (basicOpen p₁ U) (basicOpen p₂ U) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro q ⟨⟨η₁, hη₁U, hq₁⟩, ⟨η₂, hη₂U, hq₂⟩⟩
  apply hne
  obtain ⟨xp₁, c₁⟩ := p₁
  obtain ⟨xp₂, c₂⟩ := p₂
  simp only at hp_eq
  subst hp_eq
  refine Sigma.ext rfl ?_
  simp only [heq_eq_eq] at hq₁ hq₂ ⊢
  have hloopU : ∀ t, (η₂.trans η₁.symm) t ∈ U := by
    intro t
    erw [Path.trans_apply]
    split_ifs with h
    · exact hη₂U _
    · rw [Path.symm_apply]; exact hη₁U _
  have hloop_null :
      (⟦η₂.trans η₁.symm⟧ : _root_.Path.Homotopic.Quotient xp₁ xp₁) =
        ⟦_root_.Path.refl xp₁⟧ := hUloops _ hloopU
  have hbase : c₁.trans (_root_.Path.Homotopic.Quotient.mk η₁) =
      c₂.trans (_root_.Path.Homotopic.Quotient.mk η₂) := hq₁.symm.trans hq₂
  have hloop_q :
      _root_.Path.Homotopic.Quotient.trans
          (_root_.Path.Homotopic.Quotient.mk η₂)
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) =
      _root_.Path.Homotopic.Quotient.refl xp₁ := by
    have h := hloop_null
    change _root_.Path.Homotopic.Quotient.mk (η₂.trans η₁.symm) =
           _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl xp₁) at h
    rw [_root_.Path.Homotopic.Quotient.mk_trans,
        _root_.Path.Homotopic.Quotient.mk_symm,
        _root_.Path.Homotopic.Quotient.mk_refl] at h
    exact h
  calc c₁
      = (c₁.trans (_root_.Path.Homotopic.Quotient.mk η₁)).trans
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) := by
            rw [_root_.Path.Homotopic.Quotient.trans_assoc,
                _root_.Path.Homotopic.Quotient.trans_symm,
                _root_.Path.Homotopic.Quotient.trans_refl]
    _ = (c₂.trans (_root_.Path.Homotopic.Quotient.mk η₂)).trans
          (_root_.Path.Homotopic.Quotient.symm
            (_root_.Path.Homotopic.Quotient.mk η₁)) := by rw [hbase]
    _ = c₂.trans
          (_root_.Path.Homotopic.Quotient.trans
            (_root_.Path.Homotopic.Quotient.mk η₂)
            (_root_.Path.Homotopic.Quotient.symm
              (_root_.Path.Homotopic.Quotient.mk η₁))) :=
            _root_.Path.Homotopic.Quotient.trans_assoc c₂ _ _
    _ = c₂.trans (_root_.Path.Homotopic.Quotient.refl xp₁) := by rw [hloop_q]
    _ = c₂ := _root_.Path.Homotopic.Quotient.trans_refl c₂


omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_exhaust
    (x : X) {U : Set X} (hxU : x ∈ U) (hUpc : IsPathConnected U)
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
    (hq : q.1 ∈ U) :
    ∃ (p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)
      (_hp_eq : p.1 = x),
      q ∈ basicOpen p U := by
  have hjoined : JoinedIn U x q.1 := hUpc.joinedIn _ hxU _ hq
  set ζ : _root_.Path x q.1 := hjoined.somePath
  have hζU : ∀ t, ζ t ∈ U := fun t => hjoined.somePath_mem t
  refine ⟨⟨x, q.2.trans (_root_.Path.Homotopic.Quotient.mk ζ.symm)⟩, rfl, ?_⟩
  refine ⟨ζ, hζU, ?_⟩
  rw [_root_.Path.Homotopic.Quotient.trans_assoc]
  conv_lhs => rw [← _root_.Path.Homotopic.Quotient.trans_refl q.2]
  congr 1
  rw [show (_root_.Path.Homotopic.Quotient.mk ζ.symm) =
      _root_.Path.Homotopic.Quotient.symm (_root_.Path.Homotopic.Quotient.mk ζ) from rfl,
    _root_.Path.Homotopic.Quotient.symm_trans]


omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
private theorem uc_sheet_proj_isOpenMap
    {p : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X}
    {U : Set X} (hU : IsOpen U)
    {O : Set
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)}
    (hOopen : IsOpen O) (hOsub : O ⊆ basicOpen p U) :
    IsOpen ((proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
        '' O) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨q, hqO, rfl⟩
  have hqUp : q ∈ basicOpen p U := hOsub hqO
  have hqU : q.1 ∈ U := by
    obtain ⟨η, hη, _⟩ := hqUp
    simpa [proj] using hη 1
  have hO_nhd : O ∈ nhds q := hOopen.mem_nhds hqO
  have hbasis := (basis_assemble (X := X)).nhds_hasBasis (a := q)
  obtain ⟨S, ⟨⟨r, V, hVopen, hrV, rfl⟩, hqV⟩, hVsub⟩ := hbasis.mem_iff.mp hO_nhd
  obtain ⟨W, hWopen, hqW, _hWsub, hWpc, hWshrink⟩ :=
    basis_intersection (p₁ := r) (p₂ := p) (r := q)
      hVopen hU ⟨hqV, hqUp⟩
  have hsub : basicOpen q W ⊆ O :=
    (hWshrink).trans (fun s hs => hVsub hs.1)
  refine Filter.mem_of_superset (hWopen.mem_nhds hqW) ?_
  intro z hzW
  have hjoined : JoinedIn W q.1 z := hWpc.joinedIn _ hqW _ hzW
  refine ⟨⟨z, q.2.trans (_root_.Path.Homotopic.Quotient.mk hjoined.somePath)⟩, ?_, rfl⟩
  apply hsub
  refine ⟨hjoined.somePath, hjoined.somePath_mem, rfl⟩

omit [ConnectedSpace X] in
theorem proj_isCoveringMap :
    IsCoveringMap (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) := by
  intro x
  obtain ⟨U, hUopen, hxU, hUpc, hUloops⟩ := uc_good_nhd_exists (X := X) x
  set Fx : Set
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
    (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' {x} with hFxdef
  have hp1_eq (p : Fx) : (p.1 : _).1 = x := p.2
  have hp1_mem (p : Fx) : (p.1 : _).1 ∈ U := by rw [hp1_eq p]; exact hxU
  let sheet : Fx → Set
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :=
    fun p => basicOpen p.1 U
  have hsheet_open : ∀ p : Fx, IsOpen (sheet p) := fun p =>
    TopologicalSpace.GenerateOpen.basic _ ⟨p.1, U, hUopen, hp1_mem p, rfl⟩
  have hsheet_sub_preU : ∀ p : Fx, sheet p ⊆
      (proj :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
        ⁻¹' U := by
    intro p q hq
    obtain ⟨η, hη, _⟩ := hq
    have := hη 1
    change q.1 ∈ U
    rw [Path.target] at this
    exact this
  have hself_in_sheet : ∀ p : Fx, p.1 ∈ sheet p := by
    intro p
    refine ⟨_root_.Path.refl p.1.1, fun _ => hp1_mem p, ?_⟩
    have hmkrefl :
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl p.1.1) :
            _root_.Path.Homotopic.Quotient p.1.1 p.1.1)
          = _root_.Path.Homotopic.Quotient.refl p.1.1 :=
      _root_.Path.Homotopic.Quotient.mk_refl p.1.1
    rw [hmkrefl]
    exact (_root_.Path.Homotopic.Quotient.trans_refl p.1.2).symm
  have hsheet_disj : Pairwise (Disjoint on sheet) := by
    intro p₁ p₂ hp
    have hne : p₁.1 ≠ p₂.1 := fun h => hp (Subtype.ext h)
    have heq : p₁.1.1 = p₂.1.1 := (hp1_eq p₁).trans (hp1_eq p₂).symm
    have hloops₁ : ∀ γ : _root_.Path p₁.1.1 p₁.1.1, (∀ t, γ t ∈ U) →
        (⟦γ⟧ : _root_.Path.Homotopic.Quotient p₁.1.1 p₁.1.1) =
          ⟦_root_.Path.refl p₁.1.1⟧ := by
      have hbase : p₁.1.1 = x := hp1_eq p₁
      intro γ hγ
      revert γ
      rw [hbase]
      exact hUloops
    exact uc_sheet_disjoint (hp1_mem p₁) (hp1_mem p₂) heq hloops₁ hne
  have hsheet_exhaust : ∀ q ∈ (proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U, ∃ p : Fx, q ∈ sheet p := by
    intro q hq
    obtain ⟨p, hp_eq, hqsheet⟩ := uc_sheet_exhaust (X := X) x hxU hUpc q hq
    have hp_mem : p ∈ Fx := by
      change p.1 = x
      exact hp_eq
    refine ⟨⟨p, hp_mem⟩, ?_⟩
    exact hqsheet
  have hsheet_bij : ∀ p : Fx, Set.BijOn proj (sheet p) U := by
    intro p
    refine uc_sheet_bijection_on_good_U p.1 U (hp1_mem p) hUpc ?_
    intro γ hγ
    have hbase : p.1.1 = x := hp1_eq p
    revert γ
    rw [hbase]
    exact hUloops
  have hsheet_inj : ∀ p : Fx, (sheet p).InjOn proj := fun p => (hsheet_bij p).2.1
  have hsheet_surj : ∀ p : Fx, (sheet p).SurjOn proj U := fun p => (hsheet_bij p).2.2
  have hFx_disc : DiscreteTopology Fx := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro p
    have hsingleton_eq :
        ({p} : Set Fx) = Subtype.val ⁻¹' (sheet p) := by
      ext q
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · intro hqp
        rw [hqp]
        exact hself_in_sheet p
      · intro hqp
        by_contra hne
        have hne' : q ≠ p := hne
        have hdisj : Disjoint (sheet q) (sheet p) := hsheet_disj hne'
        rw [Set.disjoint_iff_inter_eq_empty] at hdisj
        have hq_in_own : q.1 ∈ sheet q := hself_in_sheet q
        have hqinter : q.1 ∈ sheet q ∩ sheet p := ⟨hq_in_own, hqp⟩
        rw [hdisj] at hqinter
        exact hqinter
    rw [hsingleton_eq]
    exact (hsheet_open p).preimage continuous_subtype_val
  refine ⟨hFx_disc, U, hxU, hUopen, hUopen.preimage proj_continuous, ?_⟩
  classical
  let theSheet : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) → Fx := fun q => (hsheet_exhaust q.1 q.2).choose
  have htheSheet_mem : ∀ q, q.1 ∈ sheet (theSheet q) := fun q =>
    (hsheet_exhaust q.1 q.2).choose_spec
  have htheSheet_uniq : ∀ (q : _) (p : Fx),
      q.1 ∈ sheet p → theSheet q = p := by
    intro q p hqp
    by_contra hne
    have hdisj : Disjoint (sheet (theSheet q)) (sheet p) := hsheet_disj hne
    rw [Set.disjoint_iff_inter_eq_empty] at hdisj
    have hmem : q.1 ∈ sheet (theSheet q) ∩ sheet p := ⟨htheSheet_mem q, hqp⟩
    rw [hdisj] at hmem
    exact hmem
  let theInv : (U × Fx) → ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) := fun yp =>
    ⟨(hsheet_surj yp.2 yp.1.2).choose, by
      have := (hsheet_surj yp.2 yp.1.2).choose_spec.1
      exact hsheet_sub_preU yp.2 this⟩
  have htheInv_mem : ∀ yp, (theInv yp).1 ∈ sheet yp.2 := fun yp =>
    (hsheet_surj yp.2 yp.1.2).choose_spec.1
  have htheInv_proj : ∀ yp, proj (theInv yp).1 = yp.1.1 := fun yp =>
    (hsheet_surj yp.2 yp.1.2).choose_spec.2
  let fwd : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) → (U × Fx) :=
    fun q => (⟨q.1.1, q.2⟩, theSheet q)
  let inv : (U × Fx) → ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) := theInv
  have h_left_inv : ∀ q, inv (fwd q) = q := by
    intro q
    apply Subtype.ext
    have hmem1 := htheInv_mem (⟨q.1.1, q.2⟩, theSheet q)
    have hproj1 := htheInv_proj (⟨q.1.1, q.2⟩, theSheet q)
    have hmem2 := htheSheet_mem q
    apply (hsheet_inj (theSheet q)) hmem1 hmem2 hproj1
  have h_right_inv : ∀ yp, fwd (inv yp) = yp := by
    rintro ⟨⟨y, hy⟩, p⟩
    have hproj : proj (inv (⟨y, hy⟩, p)).1 = y := htheInv_proj (⟨y, hy⟩, p)
    have hsheet_mem : (inv (⟨y, hy⟩, p)).1 ∈ sheet p := htheInv_mem (⟨y, hy⟩, p)
    have h_eq_sheet : theSheet (inv (⟨y, hy⟩, p)) = p :=
      htheSheet_uniq _ p hsheet_mem
    apply Prod.ext
    · apply Subtype.ext
      change (inv (⟨y, hy⟩, p)).1.1 = y
      exact hproj
    · simpa [fwd] using h_eq_sheet
  have hfwd_cont : Continuous fwd := by
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      exact (proj_continuous (X := X)).comp continuous_subtype_val
    · rw [continuous_discrete_rng]
      intro p
      have h_eq : (theSheet ⁻¹' {p} :
          Set ((proj :
              DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X
              → X) ⁻¹' U)) =
          Subtype.val ⁻¹' sheet p := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hq
          rw [← hq]
          exact htheSheet_mem q
        · intro hq
          exact htheSheet_uniq q p hq
      rw [h_eq]
      exact (hsheet_open p).preimage continuous_subtype_val
  have hinv_cont : Continuous inv := by
    apply continuous_induced_rng.mpr
    have hcont : Continuous fun yp : U × Fx => (inv yp).1 := by
      apply continuous_prod_of_discrete_right.mpr
      intro p
      refine continuous_iff_continuousAt.mpr ?_
      intro y₀
      rw [ContinuousAt, Filter.tendsto_def]
      intro W hW
      set q₀ := (inv (y₀, p)).1
      have hq₀_in_sheet : q₀ ∈ sheet p := htheInv_mem (y₀, p)
      have hproj_q₀ : proj q₀ = y₀.1 := htheInv_proj (y₀, p)
      rw [_root_.mem_nhds_iff] at hW
      obtain ⟨W', hW'sub, hW'open, hq₀W'⟩ := hW
      set W'' := W' ∩ sheet p
      have hW''open : IsOpen W'' := hW'open.inter (hsheet_open p)
      have hq₀W'' : q₀ ∈ W'' := ⟨hq₀W', hq₀_in_sheet⟩
      have hprojW''_open : IsOpen (proj '' W'') :=
        uc_sheet_proj_isOpenMap hUopen hW''open
          (Set.inter_subset_right)
      have hy₀_inW'' : y₀.1 ∈ proj '' W'' := ⟨q₀, hq₀W'', hproj_q₀⟩
      refine Filter.mem_of_superset
        ((continuous_subtype_val.continuousAt
          (x := y₀)).preimage_mem_nhds
          (hprojW''_open.mem_nhds hy₀_inW'')) ?_
      intro y hy
      obtain ⟨q', hq'W'', hq'proj⟩ := hy
      have h_eq : (inv (y, p)).1 = q' := by
        apply hsheet_inj p (htheInv_mem (y, p)) hq'W''.2
        rw [htheInv_proj (y, p), hq'proj]
      change (inv (y, p)).1 ∈ W
      rw [h_eq]
      exact hW'sub hq'W''.1
    exact hcont
  let eqv : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) ≃ (U × Fx) :=
  { toFun := fwd, invFun := inv, left_inv := h_left_inv, right_inv := h_right_inv }
  let homeo : ((proj :
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X)
      ⁻¹' U) ≃ₜ (U × Fx) :=
  { toEquiv := eqv, continuous_toFun := hfwd_cont, continuous_invFun := hinv_cont }
  refine ⟨homeo, ?_⟩
  intro q
  rfl

def basePoint :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X :=
  ⟨(default : X),
    _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X))⟩

def ucSubpathLift {x : X} (γ : _root_.Path (default : X) x)
    (s : unitInterval) :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X :=
  ⟨γ s,
    (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl⟩

omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_continuous {x : X} (γ : _root_.Path (default : X) x) :
    Continuous (ucSubpathLift γ) := by
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  rw [ContinuousAt, Filter.tendsto_def]
  intro N hN
  obtain ⟨S, ⟨⟨p, V, hVopen, hpV, rfl⟩, hTs₀S⟩, hSN⟩ :=
    (basis_assemble (X := X)).nhds_hasBasis.mem_iff.mp hN
  rcases p with ⟨p, hp⟩
  obtain ⟨η₀, hη₀V, hη₀eq⟩ := hTs₀S
  change _root_.Path p (γ s₀) at η₀
  simp only [ucSubpathLift] at hη₀eq
  have hcont_fam :
      Continuous (fun st : unitInterval × unitInterval =>
        γ.subpath s₀ st.1 st.2) := by
    have hmap : Continuous
        (fun st : unitInterval × unitInterval =>
          (s₀, st.1, st.2) : unitInterval × unitInterval →
            unitInterval × unitInterval × unitInterval) := by
      exact (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    exact γ.subpath_continuous_family.comp hmap
  have hopen : IsOpen
      {st : unitInterval × unitInterval | γ.subpath s₀ st.1 st.2 ∈ V} :=
    hVopen.preimage hcont_fam
  have hsub : ({s₀} ×ˢ (Set.univ : Set unitInterval)) ⊆
      {st : unitInterval × unitInterval | γ.subpath s₀ st.1 st.2 ∈ V} := by
    rintro ⟨s, t⟩ ⟨hs, -⟩
    simp only [Set.mem_singleton_iff] at hs
    simp only [Set.mem_ofPred_eq, hs, Path.subpath_self, Path.refl_apply]
    have : γ s₀ ∈ V := by
      have h := hη₀V 1
      exact η₀.target ▸ h
    exact this
  obtain ⟨J, K, hJopen, _hKopen, hs₀J, _hKuniv, hJK⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := s₀)) (isCompact_univ) hopen hsub
  have hs₀J' : s₀ ∈ J := hs₀J rfl
  have hsubV : ∀ s ∈ J, ∀ t, γ.subpath s₀ s t ∈ V := by
    intro s hs t
    have : (s, t) ∈ J ×ˢ K := ⟨hs, _hKuniv (Set.mem_univ t)⟩
    exact hJK this
  refine Filter.mem_of_superset (hJopen.mem_nhds hs₀J') ?_
  intro s hsJ
  apply hSN
  unfold ucSubpathLift
  refine ⟨η₀.trans (γ.subpath s₀ s), ?_, ?_⟩
  · intro t
    rw [Path.trans_apply]
    split_ifs with h
    · exact hη₀V _
    · rw [Path.subpath]
      exact hsubV s hsJ _
  · change (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl =
      hp.trans (_root_.Path.Homotopic.Quotient.mk (η₀.trans (γ.subpath s₀ s)))
    have hadd :
        (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)
            : _root_.Path.Homotopic.Quotient (γ 0) (γ s)) =
          (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s₀)).trans
            (_root_.Path.Homotopic.Quotient.mk (γ.subpath s₀ s)) := by
      rw [← _root_.Path.Homotopic.Quotient.mk_trans]
      exact (_root_.Path.Homotopic.Quotient.eq.mpr
        ⟨Path.Homotopy.subpathTransSubpath γ 0 s₀ s⟩).symm
    have hcast :
        (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s)).cast γ.source.symm rfl =
          ((_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 s₀)).cast γ.source.symm rfl).trans
            (_root_.Path.Homotopic.Quotient.mk (γ.subpath s₀ s)) := by
      rw [hadd]
      rfl
    erw [hcast, hη₀eq, _root_.Path.Homotopic.Quotient.mk_trans]
    exact _root_.Path.Homotopic.Quotient.trans_assoc _ _ _


omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_zero {x : X} (γ : _root_.Path (default : X) x) :
    ucSubpathLift γ 0 = basePoint := by
  change (⟨γ 0,
      (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 0)).cast γ.source.symm rfl⟩ :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) = basePoint
  have h0 : (γ 0 : X) = default := γ.source
  refine Sigma.ext h0 ?_
  rw [show (basePoint (X := X)).2 =
      _root_.Path.Homotopic.Quotient.mk (Path.refl (default : X)) from rfl,
    ← _root_.Path.Homotopic.Quotient.mk_cast]
  refine Path.Homotopic.hpath_hext ?_
  intro t
  rw [Path.cast_coe, Path.refl_apply, Path.subpath, Path.coe_mk_mk,
    Function.comp_apply, Icc.convexComb_eq]
  exact γ.source


omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_one {x : X} (γ : _root_.Path (default : X) x) :
    ucSubpathLift γ 1 =
      ⟨x, _root_.Path.Homotopic.Quotient.mk γ⟩ := by
  change (⟨γ 1,
      (_root_.Path.Homotopic.Quotient.mk (γ.subpath 0 1)).cast γ.source.symm rfl⟩ :
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) =
    ⟨x, _root_.Path.Homotopic.Quotient.mk γ⟩
  have h1 : (γ 1 : X) = x := γ.target
  refine Sigma.ext h1 ?_
  rw [← _root_.Path.Homotopic.Quotient.mk_cast]
  refine Path.Homotopic.hpath_hext ?_
  intro t
  rw [Path.cast_coe, Path.subpath, Path.coe_mk_mk, Function.comp_apply,
    Icc.convexComb_zero_one]


omit [ConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_subpathLift_proj {x : X} (γ : _root_.Path (default : X) x)
    (s : unitInterval) : proj (ucSubpathLift γ s) = γ s := rfl

omit [ConnectedSpace X] [SemilocallySimplyConnectedSpace X] in
theorem uc_joined_basePoint
    (q : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) :
    Joined (basePoint (X := X)) q := by
  obtain ⟨x, c⟩ := q
  obtain ⟨γ, rfl⟩ := _root_.Path.Homotopic.Quotient.mk_surjective c
  exact ⟨{
    toFun := ucSubpathLift γ
    continuous_toFun := uc_subpathLift_continuous γ
    source' := uc_subpathLift_zero γ
    target' := uc_subpathLift_one γ }⟩

instance pathConnectedSpace :
    PathConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) where
  nonempty := ⟨basePoint⟩
  joined x y := (uc_joined_basePoint x).symm.trans (uc_joined_basePoint y)

omit [ConnectedSpace X] in
theorem uc_basePoint_loops_nullhomotopic
    (δ : _root_.Path (basePoint (X := X)) basePoint) :
    _root_.Path.Homotopic δ (_root_.Path.refl basePoint) := by
  have hproj : proj (basePoint (X := X)) = default := rfl
  set γX : C(unitInterval, X) :=
    ⟨proj ∘ δ, proj_continuous.comp δ.continuous⟩ with hγXdef
  have hcov : IsCoveringMap
      (proj : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X → X) :=
    UniversalCover.proj_isCoveringMap
  set γ : _root_.Path (default : X) default :=
    { toFun := proj ∘ δ
      continuous_toFun := proj_continuous.comp δ.continuous
      source' := by
        change proj (δ 0) = default
        rw [δ.source]; rfl
      target' := by
        change proj (δ 1) = default
        rw [δ.target]; rfl } with hγdef
  have hγX0 : γX 0 = proj basePoint := by
    rw [hγXdef]
    change proj (δ 0) = proj basePoint
    rw [δ.source]
  have hδlift : (⟨δ, δ.continuous⟩ : C(unitInterval,
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)) =
      hcov.liftPath γX basePoint hγX0 := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t; rfl
    · exact δ.source
  have hSlift : (⟨ucSubpathLift γ, uc_subpathLift_continuous γ⟩ : C(unitInterval,
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X)) =
      hcov.liftPath γX basePoint hγX0 := by
    rw [hcov.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext t
      simp only [ContinuousMap.coe_mk, Function.comp_apply, hγXdef]
      exact uc_subpathLift_proj γ t
    · exact uc_subpathLift_zero γ
  have hδeq : (δ : unitInterval →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) =
      ucSubpathLift γ := by
    have := hδlift.trans hSlift.symm
    exact congrArg (fun f : C(unitInterval, _) => (f : unitInterval → _)) this
  have hend : (basePoint (X := X)) =
      (⟨default, _root_.Path.Homotopic.Quotient.mk γ⟩ :
        DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) := by
    have h1 : δ 1 = ucSubpathLift γ 1 := congrFun hδeq 1
    rw [uc_subpathLift_one] at h1
    rw [← h1, δ.target]
  have hclass : (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X))) =
      _root_.Path.Homotopic.Quotient.mk γ := by
    have hsnd := (Sigma.ext_iff.mp hend).2
    exact eq_of_heq hsnd
  have hmapInj := hcov.injective_path_homotopic_map basePoint basePoint
  rw [← _root_.Path.Homotopic.Quotient.eq]
  apply hmapInj
  change (_root_.Path.Homotopic.Quotient.mk δ).map ⟨proj, proj_continuous⟩ =
    (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl basePoint)).map ⟨proj, proj_continuous⟩
  rw [← _root_.Path.Homotopic.Quotient.mk_map, ← _root_.Path.Homotopic.Quotient.mk_map]
  have hδmap : (_root_.Path.Homotopic.Quotient.mk
      (δ.map (proj_continuous (X := X)))) =
      _root_.Path.Homotopic.Quotient.mk γ := by
    refine _root_.Path.Homotopic.Quotient.eq.mpr ?_
    exact ⟨Path.Homotopy.refl _⟩
  have hreflmap : (_root_.Path.Homotopic.Quotient.mk
      ((_root_.Path.refl (basePoint (X := X))).map (proj_continuous (X := X)))) =
      _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl (default : X)) := by
    refine _root_.Path.Homotopic.Quotient.eq.mpr ?_
    exact ⟨Path.Homotopy.refl _⟩
  rw [hδmap, hreflmap, hclass]

instance simplyConnectedSpace :
    SimplyConnectedSpace
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover X) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, fun e γ => ?_⟩
  set β : _root_.Path (basePoint (X := X)) e := (uc_joined_basePoint e).somePath with hβ
  set δ : _root_.Path (basePoint (X := X)) basePoint :=
    β.trans (γ.trans β.symm) with hδ
  have hδnull := uc_basePoint_loops_nullhomotopic δ
  rw [← _root_.Path.Homotopic.Quotient.eq] at hδnull ⊢
  have hδquot :
      (_root_.Path.Homotopic.Quotient.mk δ) =
        (_root_.Path.Homotopic.Quotient.mk β).trans
          ((_root_.Path.Homotopic.Quotient.mk γ).trans
            (_root_.Path.Homotopic.Quotient.symm
              (_root_.Path.Homotopic.Quotient.mk β))) := by
    rw [hδ]
    simp only [_root_.Path.Homotopic.Quotient.mk_trans, _root_.Path.Homotopic.Quotient.mk_symm]
  rw [hδquot, _root_.Path.Homotopic.Quotient.mk_refl] at hδnull
  rw [_root_.Path.Homotopic.Quotient.mk_refl]
  set B := _root_.Path.Homotopic.Quotient.mk β with hB
  set G := _root_.Path.Homotopic.Quotient.mk γ with hG
  have key : (B.symm.trans (B.trans (G.trans B.symm))).trans B = G := by
    rw [← _root_.Path.Homotopic.Quotient.trans_assoc,
      ← _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.refl_trans,
      _root_.Path.Homotopic.Quotient.trans_assoc,
      _root_.Path.Homotopic.Quotient.symm_trans,
      _root_.Path.Homotopic.Quotient.trans_refl]
  calc G
      = (B.symm.trans (B.trans (G.trans B.symm))).trans B := key.symm
    _ = (B.symm.trans (_root_.Path.Homotopic.Quotient.refl basePoint)).trans B := by
          rw [hδnull]
    _ = _root_.Path.Homotopic.Quotient.refl e := by
          rw [_root_.Path.Homotopic.Quotient.trans_refl,
            _root_.Path.Homotopic.Quotient.symm_trans]

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end

/- Source module: Fiber/Equivalence.lean -/

open Set Function
open scoped Topology

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Topology
namespace UniversalCover

theorem isCoveringMap_fibre_finite_of_compact
    {X E : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace E] [CompactSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) :
    Finite (p ⁻¹' {x} : Set E) := by
  have hdisc : DiscreteTopology (p ⁻¹' {x} : Set E) :=
    (hp x).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {x} : Set E) :=
    isClosed_singleton.preimage hp.continuous
  have hcomp : CompactSpace (p ⁻¹' {x} : Set E) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact finite_of_compact_of_discrete

theorem action_eval_surjective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Surjective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  intro e''
  obtain ⟨e'v, he'v⟩ := e'
  obtain ⟨e''v, he''v⟩ := e''
  have he' : p e'v = x := he'v
  subst he'
  have he'' : p e''v = p e'v := he''v
  obtain ⟨δ⟩ := PathConnectedSpace.joined e'v e''v
  set η : Path (p e'v) (p e'v) :=
    (δ.map hp.continuous).cast rfl he''.symm with hη_def
  refine ⟨Path.Homotopic.Quotient.mk η, ?_⟩
  apply Subtype.ext
  have hcomp_fun' : p ∘ (δ : unitInterval → E) = (η : unitInterval → X) := by
    funext t; rfl
  have hη_zero : (η : unitInterval → X) 0 = p e'v := η.source
  have hlift_eq :
      hp.liftPath (η : C(unitInterval, X)) e'v hη_zero = δ.toContinuousMap := by
    symm
    refine (hp.eq_liftPath_iff' hη_zero).mpr ⟨?_, δ.source⟩
    exact hcomp_fun'
  have hval :
      (hp.liftPath (η : C(unitInterval, X)) e'v hη_zero) 1 = e''v := by
    have := congrArg (fun f : C(unitInterval, E) => f 1) hlift_eq
    simpa using this.trans δ.target
  exact hval

theorem action_eval_injective
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    Function.Injective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e') := by
  refine fun γ₁ γ₂ heq => ?_
  induction γ₁ using Path.Homotopic.Quotient.ind with | _ p₁ =>
  induction γ₂ using Path.Homotopic.Quotient.ind with | _ p₂ =>
  rw [Path.Homotopic.Quotient.eq]
  have he' : p (e' : E) = x := e'.2
  set Γ₁ : C(unitInterval, E) := hp.liftPath p₁.toContinuousMap (e' : E)
    (p₁.source.trans he'.symm) with hΓ₁
  set Γ₂ : C(unitInterval, E) := hp.liftPath p₂.toContinuousMap (e' : E)
    (p₂.source.trans he'.symm) with hΓ₂
  have hΓ₁_zero : Γ₁ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hΓ₂_zero : Γ₂ 0 = (e' : E) := hp.liftPath_zero _ _ _
  have hends : Γ₁ 1 = Γ₂ 1 := by
    have hmono : (hp.monodromy (Path.Homotopic.Quotient.mk p₁) e' : E) =
        (hp.monodromy (Path.Homotopic.Quotient.mk p₂) e' : E) :=
      congrArg Subtype.val heq
    change (Γ₁ : unitInterval → E) 1 = (Γ₂ : unitInterval → E) 1
    exact hmono
  let π₁ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₁
      source' := hΓ₁_zero
      target' := rfl }
  let π₂ : Path (e' : E) (Γ₁ 1) :=
    { toContinuousMap := Γ₂
      source' := hΓ₂_zero
      target' := hends.symm }
  obtain ⟨H⟩ : Path.Homotopic π₁ π₂ := SimplyConnectedSpace.paths_homotopic π₁ π₂
  have hΓ_rel : ContinuousMap.HomotopicRel Γ₁ Γ₂ {0, 1} := ⟨H⟩
  have hp_comp : ContinuousMap.HomotopicRel
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁)
      ((⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂) {0, 1} :=
    hΓ_rel.comp_continuousMap _
  have hp_eq₁ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₁ = p₁.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  have hp_eq₂ : (⟨p, hp.continuous⟩ : C(E, X)).comp Γ₂ = p₂.toContinuousMap := by
    ext t
    exact congr_fun (hp.liftPath_lifts _ _ _) t
  rw [hp_eq₁, hp_eq₂] at hp_comp
  exact hp_comp

noncomputable def fibreEquivLoopQuotient
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ Path.Homotopic.Quotient x x :=
  (Equiv.ofBijective
      (fun γ : Path.Homotopic.Quotient x x => hp.monodromy γ e')
      ⟨action_eval_injective hp x e', action_eval_surjective hp x e'⟩).symm

noncomputable def fibreEquivFundamentalGroup
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    [PathConnectedSpace E] [SimplyConnectedSpace E]
    {p : E → X} (hp : IsCoveringMap p) (x : X) (e' : p ⁻¹' {x}) :
    (p ⁻¹' {x}) ≃ FundamentalGroup X x :=
  (fibreEquivLoopQuotient hp x e').trans
    { toFun := FundamentalGroup.fromPath
      invFun := FundamentalGroup.toPath
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finite_pi1_of_uc
    {X : Type*} [TopologicalSpace X] [T1Space X] [Inhabited X]
    [LocallyPathConnectedSpace X]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace X]
    [CompactSpace (UniversalCover X)] :
    Finite (FundamentalGroup X (default : X)) := by
  let : Finite
      ((proj : UniversalCover X → X) ⁻¹' {(default : X)}) :=
    isCoveringMap_fibre_finite_of_compact
      (UniversalCover.proj_isCoveringMap (X := X)) default
  let e : (proj : UniversalCover X → X) ⁻¹' {(default : X)} :=
    ⟨basePoint (X := X), rfl⟩
  exact Finite.of_equiv _
    (fibreEquivFundamentalGroup
      (UniversalCover.proj_isCoveringMap (X := X)) default e)

end UniversalCover
end Topology
end Riemannian
end Geometry
end DifferentialGeometry

end


open Set Manifold
open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Riemannian.Topology

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R2_H2_R1.H1 := by
  intro M _ _ _ _ finitePi
  let : Inhabited M := ⟨Classical.ofNonempty⟩
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  let : SemilocallySimplyConnectedSpace M := manifold_semilocallySimplyConnectedSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
  let E := UniversalCover M
  let p : E → M := UniversalCover.proj
  have hp : IsCoveringMap p := UniversalCover.proj_isCoveringMap
  have hc : SimplyConnectedSpace E := UniversalCover.simplyConnectedSpace
  refine ⟨E, inferInstance, hc, p, hp, ?_⟩
  intro x
  obtain ⟨path⟩ := PathConnectedSpace.joined (default : M) x
  let e : p ⁻¹' {x} := ⟨⟨x, Path.Homotopic.Quotient.mk path⟩, rfl⟩
  let : Finite (FundamentalGroup M x) := finitePi x
  exact Finite.of_equiv _ (UniversalCover.fibreEquivFundamentalGroup hp x e).symm



/-
DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

The files under DifferentialGeometry/External/Schoenflies derive from
https://github.com/alonamaloh/schoenflies-lean
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under the Apache License 2.0.
See that directory's LICENSE, MODIFICATIONS.md and provenance records.

The selected source under DifferentialGeometry/External/TauCeti derives from
https://github.com/TauCetiProject/TauCeti
revision 3358033ba2fd35f321356dceaf2372a0fd6c0bfd.
Copyright (c) 2026 Joseph Tooby-Smith and The Tau Ceti contributors.
Authors include Joseph Tooby-Smith, Codex and The Tau Ceti contributors,
as recorded in the preserved original source headers.
Released under the Apache License 2.0.
See that directory's LICENSE, SOURCE_MAP.json and MODIFICATIONS.md.
Native Sard, Morse, embedding and extension modules consume this external API.

The source under DifferentialGeometry/External/CanonicalTopology is restored
from the canonical-topology/Poincare project by Ayush Khaitan and its
contributors. See its pinned source archives, SOURCE_MAP.json, LICENSE
and MODIFICATIONS.md for exact revisions and declaration-level adaptations.
The derivative homotopy includes adapted source from plby/HopfProblem,
Solution.lean at 9ac8a456b526527837d7082ff775213ca8bc9809, lines 62156–62228,
under Apache-2.0; the nested attribution and license are preserved.

The source under DifferentialGeometry/External/ClassificationOfSurfaces
derives from https://github.com/mccorvie/classification-of-surfaces.
It includes work by the ClassificationOfSurfaces contributors, Steven Sivek
and Kai Lam, as recorded in the original source and nested provenance.
Released under the Apache License 2.0. See its LICENSE and MODIFICATIONS.md.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
