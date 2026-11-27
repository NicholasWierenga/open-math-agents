import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.Homotopy.Lifting

/-!
The orientation-cover construction is adapted from DifferentialGeometry v0.1.3
by Ziyang Qin, Yuan Liao, Ayush Khaitan, Bennett Chow and contributors,
revision 7a48598d35109aa99d1cc678e2724c213cdf4ff3, Apache-2.0.
The source modules are combined and specialized to the tangent bundle of a
smooth Euclidean three-manifold.
-/

noncomputable section

/- Source module Bundle/Orientation/Classes.lean -/
section
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem map_orientation_eq_iff (hdim : Module.finrank ℝ V = n)
    (o : Orientation ℝ V (Fin n)) (A : V ≃ₗ[ℝ] V) :
    Orientation.map (Fin n) A o = o ↔ 0 < LinearMap.det (A : V →ₗ[ℝ] V) :=
  o.map_eq_iff_det_pos A (by simpa using hdim.symm)

end DifferentialGeometry.VectorBundle
end

/- Source module Bundle/Orientation/Transport.lean -/
section
open scoped Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X]


abbrev orientationTopology : TopologicalSpace (Orientation ℝ V (Fin n)) := ⊥

local instance : TopologicalSpace (Orientation ℝ V (Fin n)) := orientationTopology
local instance : DiscreteTopology (Orientation ℝ V (Fin n)) := ⟨rfl⟩

theorem continuous_orientation_transport (hdim : Module.finrank ℝ V = n)
    (A : X → V ≃L[ℝ] V) (hA : Continuous (fun x => (A x : V →L[ℝ] V))) :
    Continuous (fun z : X × Orientation ℝ V (Fin n) =>
      Orientation.map (Fin n) (A z.1).toLinearEquiv z.2) := by
  have hdet : Continuous (fun z : X × Orientation ℝ V (Fin n) =>
      (A z.1 : V →L[ℝ] V).det) :=
    (ContinuousLinearMap.continuous_det.comp hA).comp continuous_fst
  rw [continuous_iff_continuousAt]
  intro z
  have hne : (A z.1 : V →L[ℝ] V).det ≠ 0 :=
    (A z.1).toLinearEquiv.isUnit_det'.ne_zero
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hn : ∀ᶠ w in 𝓝 z, (A w.1 : V →L[ℝ] V).det < 0 :=
      hdet.continuousAt.eventually_lt_const hneg
    apply ((continuous_of_discreteTopology : Continuous (fun o : Orientation ℝ V (Fin n) => -o)).comp continuous_snd).continuousAt.congr_of_eventuallyEq
    exact hn.mono (fun w hw =>
      ((w.2).map_eq_neg_iff_det_neg (A w.1).toLinearEquiv (by simpa using hdim.symm)).mpr hw)
  · have hp : ∀ᶠ w in 𝓝 z, 0 < (A w.1 : V →L[ℝ] V).det :=
      hdet.continuousAt.eventually_const_lt hpos
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    exact hp.mono (fun w hw => (map_orientation_eq_iff hdim w.2 (A w.1).toLinearEquiv).mpr hw)


theorem continuousOn_orientation_transport (hdim : Module.finrank ℝ V = n)
    (A : X → V ≃L[ℝ] V) {s : Set X}
    (hA : ContinuousOn (fun x => (A x : V →L[ℝ] V)) s) :
    ContinuousOn (fun z : X × Orientation ℝ V (Fin n) =>
      Orientation.map (Fin n) (A z.1).toLinearEquiv z.2) (s ×ˢ Set.univ) := by
  have hA' := continuousOn_iff_continuous_domRestrict.mp hA
  have h := continuous_orientation_transport hdim (fun x : s => A x) hA'
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun z : s ×ˢ (Set.univ : Set (Orientation ℝ V (Fin n))) =>
      (⟨z.val.1, z.property.1⟩, z.val.2) :
        s ×ˢ (Set.univ : Set (Orientation ℝ V (Fin n))) → s × Orientation ℝ V (Fin n)) :=
    (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  convert h.comp hc using 1
  rfl

end DifferentialGeometry.VectorBundle
end

/- Source module Bundle/Orientation/Cover.lean -/
section
open Set Bundle
open scoped Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {B F J : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

local instance : TopologicalSpace (Orientation ℝ F (Fin n)) := orientationTopology
local instance : DiscreteTopology (Orientation ℝ F (Fin n)) := ⟨rfl⟩

omit [FiniteDimensional ℝ F] in
theorem map_orientation_trans (A B : F ≃ₗ[ℝ] F) (o : Orientation ℝ F (Fin n)) :
    Orientation.map (Fin n) B (Orientation.map (Fin n) A o) =
      Orientation.map (Fin n) (A.trans B) o := by
  induction o using Module.Ray.ind with
  | h v hv => rfl

def orientationChange (Z : VectorBundleCore ℝ B F J) (i j : J) (x : B) :
    Orientation ℝ F (Fin n) ≃ Orientation ℝ F (Fin n) :=
  Orientation.map (Fin n) ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).toLinearEquiv


def orientationCore (Z : VectorBundleCore ℝ B F J) (hdim : Module.finrank ℝ F = n) :
    FiberBundleCore J B (Orientation ℝ F (Fin n)) where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := orientationChange Z i j x
  coordChange_self i x hx o := by
    have hid : ((Z.localTriv i).coordChangeL ℝ (Z.localTriv i) x).toLinearEquiv =
        LinearEquiv.refl ℝ F := by
      ext v
      change (Z.localTriv i).coordChangeL ℝ (Z.localTriv i) x v = v
      rw [Z.localTriv_coordChange_eq i i ⟨hx, hx⟩, Z.coordChange_self i x hx]
    simp [orientationChange, hid]
  coordChange_comp i j k x hx o := by
    have hcomp :
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x).toLinearEquiv.trans
          ((Z.localTriv j).coordChangeL ℝ (Z.localTriv k) x).toLinearEquiv =
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv k) x).toLinearEquiv := by
      ext v
      change (Z.localTriv j).coordChangeL ℝ (Z.localTriv k) x
        ((Z.localTriv i).coordChangeL ℝ (Z.localTriv j) x v) =
        (Z.localTriv i).coordChangeL ℝ (Z.localTriv k) x v
      rw [Z.localTriv_coordChange_eq i j ⟨hx.1.1, hx.1.2⟩,
        Z.localTriv_coordChange_eq j k ⟨hx.1.2, hx.2⟩,
        Z.localTriv_coordChange_eq i k ⟨hx.1.1, hx.2⟩]
      exact Z.coordChange_comp i j k x hx v
    change Orientation.map (Fin n) _ (Orientation.map (Fin n) _ o) = _
    rw [map_orientation_trans, hcomp]
    rfl
  continuousOn_coordChange i j := by
    apply continuousOn_orientation_transport hdim
    apply (Z.continuousOn_coordChange i j).congr
    intro x hx
    exact ContinuousLinearMap.ext (fun v => Z.localTriv_coordChange_eq i j hx v)


theorem orientationCore_isCoveringMap (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) : IsCoveringMap (orientationCore Z hdim).proj :=
  FiberBundle.isCoveringMap


end DifferentialGeometry.VectorBundle
end

/- Source module Bundle/Orientation/Basic.lean -/
section
open Set Bundle
open scoped Topology

namespace DifferentialGeometry.VectorBundle

variable {m : ℕ} {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (V : B → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def IsCompatibleOrientation (o : ∀ x, Orientation ℝ (V x) (Fin m)) : Prop :=
  ∀ x : B, ∃ t : Trivialization F (π F V), ∃ _ht : MemTrivializationAtlas t,
    ∃ U ∈ 𝓝 x, ∃ hU : U ⊆ t.baseSet, ∃ p : Orientation ℝ F (Fin m),
      ∀ y (hy : y ∈ U),
        Orientation.map (Fin m) (t.continuousLinearEquivAt ℝ y (hU hy)).toLinearEquiv (o y) = p

end DifferentialGeometry.VectorBundle
end

/- Source module Topology/Covering/Sections.lean -/
section
namespace DifferentialGeometry.Topology.Covering

theorem exists_unique_section {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] {p : E → B}
    (hp : IsCoveringMap p) (b : B) (e : E) (he : p e = b) :
    ∃! s : C(B, E), s b = e ∧ Function.RightInverse s p := by
  obtain ⟨s, ⟨hs, hproj⟩, huniq⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id B) b e he
  refine ⟨s, ⟨hs, congrFun hproj⟩, ?_⟩
  intro t ht
  exact huniq t ⟨ht.1, funext ht.2⟩

end DifferentialGeometry.Topology.Covering
end

/- Source module Bundle/Orientation/Section.lean -/
section
open Set Bundle
open scoped Topology
namespace DifferentialGeometry.VectorBundle

variable {n : ℕ}

variable {B F J : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

local instance : TopologicalSpace (Orientation ℝ F (Fin n)) := orientationTopology
local instance : DiscreteTopology (Orientation ℝ F (Fin n)) := ⟨rfl⟩

theorem orientationCore_localTriv (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (i : J) (x : B) (hx : x ∈ Z.baseSet i)
    (o : Orientation ℝ (Z.Fiber x) (Fin n)) :
    ((orientationCore Z hdim).localTriv i ⟨x, o⟩).2 =
      Orientation.map (Fin n) ((Z.localTriv i).continuousLinearEquivAt ℝ x hx).toLinearEquiv o := by
  change Orientation.map (Fin n)
    ((Z.localTriv (Z.indexAt x)).coordChangeL ℝ (Z.localTriv i) x).toLinearEquiv o = _
  congr 2
  apply LinearEquiv.ext
  intro v
  change (Z.localTriv (Z.indexAt x)).coordChangeL ℝ (Z.localTriv i) x v =
    (Z.localTriv i).continuousLinearEquivAt ℝ x hx v
  rw [Z.localTriv_coordChange_eq (Z.indexAt x) i ⟨Z.mem_baseSet_at x, hx⟩]
  rw [(Z.localTriv i).coe_continuousLinearEquivAt_eq (R := ℝ) hx,
    Z.localTriv_continuousLinearMapAt hx]
  rfl


theorem compatibleOrientation_of_section (Z : VectorBundleCore ℝ B F J)
    (hdim : Module.finrank ℝ F = n) (s : C(B, (orientationCore Z hdim).TotalSpace))
    (hs : Function.RightInverse s (orientationCore Z hdim).proj) :
    IsCompatibleOrientation (F := F) Z.Fiber (fun x => (s x).2) := by
  intro x
  let t := (orientationCore Z hdim).localTrivAt x
  have hxsource : s x ∈ t.source := by
    change (s x).1 ∈ Z.baseSet (Z.indexAt x)
    have hsp : (s x).1 = x := hs x
    rw [hsp]
    exact Z.mem_baseSet_at x
  have hcont : ContinuousAt (fun y => (t (s y)).2) x :=
    (t.continuousAt hxsource).snd.comp s.continuous.continuousAt
  have heq : ∀ᶠ y in 𝓝 x, (t (s y)).2 = (t (s x)).2 :=
    hcont.eventually (isOpen_discrete {((t (s x)).2)} |>.mem_nhds rfl)
  let U := Z.baseSet (Z.indexAt x) ∩ {y | (t (s y)).2 = (t (s x)).2}
  have hUx : U ∈ 𝓝 x :=
    Filter.inter_mem ((Z.isOpen_baseSet _).mem_nhds (Z.mem_baseSet_at x)) heq
  refine ⟨trivializationAt F Z.Fiber x, inferInstance, U, hUx,
    (fun y hy => hy.1), (t (s x)).2, ?_⟩
  intro y hy
  have hsy : s y = ⟨y, (s y).2⟩ := by
    cases h : s y with
    | mk b o =>
      have hb : b = y := by simpa [h] using hs y
      subst b
      rfl
  have hybase : y ∈ Z.baseSet (Z.indexAt x) := hy.1
  exact (orientationCore_localTriv Z hdim (Z.indexAt x) y hybase (s y).2).symm.trans
    (by change (t ⟨y, (s y).2⟩).2 = _; rw [← hsy]; exact hy.2)

theorem exists_compatible_orientation_of_simply_connected
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (Z : VectorBundleCore ℝ B F J) (hdim : Module.finrank ℝ F = n) :
    ∃ o : ∀ x, Orientation ℝ (Z.Fiber x) (Fin n), IsCompatibleOrientation (F := F) Z.Fiber o := by
  let b : B := Classical.choice inferInstance
  let basis : Module.Basis (Fin n) ℝ F :=
    (Module.finBasis ℝ F).reindex (finCongr hdim)
  obtain ⟨s, ⟨_, hs⟩, _⟩ := DifferentialGeometry.Topology.Covering.exists_unique_section
    (orientationCore_isCoveringMap Z hdim) b ⟨b, basis.orientation⟩ rfl
  exact ⟨fun x => (s x).2, compatibleOrientation_of_section Z hdim s hs⟩

end DifferentialGeometry.VectorBundle
end


open Bundle Manifold Set
open scoped Manifold ContDiff Topology

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R1.H1 := by
  intro M _ _ _ _
  let E := EuclideanSpace ℝ (Fin 3)
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact DifferentialGeometry.VectorBundle.exists_compatible_orientation_of_simply_connected
    (tangentBundleCore (𝓘(ℝ, E)) M) finrank_euclideanSpace_fin


end

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
