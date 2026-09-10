/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import GraphThickness.IsPlanar
public import GraphThickness.Zipper
/-!

# Zipper dual

-/
@[expose] public section

universe uV uK

variable {V : Type uV} {K : Type uK}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace VertexPLabeling

/-- Simple graphs `G` and `H` are *zipper dual* with respect to the partial vertex labeling `l`
  if `l.zipper G H` is planar. -/
def AreZipperDual (l : V →ᵥ. K) (G H : SimpleGraph V) : Prop := (l.zipper G H).IsPlanar

variable {l : V →ᵥ. K} {G H : SimpleGraph V}

--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
namespace AreZipperDual

variable {G' H' : SimpleGraph V} (h : l.AreZipperDual G H)
include h

protected lemma symm : l.AreZipperDual H G := .iso (l.zipperSymm H G) h

lemma mono_left (hG : G' ≤ G) : l.AreZipperDual G' H := .mono (l.zipper_mono_left hG H) h

lemma mono_right (hH : H' ≤ H) : l.AreZipperDual G H' := .mono (l.zipper_mono_right G hH) h

lemma mono (hG : G' ≤ G) (hH : H' ≤ H) : l.AreZipperDual G' H' := (h.mono_left hG).mono_right hH

lemma isPlanar_left : G.IsPlanar := .hom (l.zipperLeft G H) (l.zipperLeft_injective G H) h

lemma isPlanar_right : H.IsPlanar := .hom (l.zipperRight G H) (l.zipperRight_injective G H) h

end AreZipperDual
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~

end VertexPLabeling
--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~==~~--~~
