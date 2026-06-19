import Hammer

namespace HammerCases.MissingIndDef

inductive A : Type

inductive B : A -> Prop where
  | b x : B x

example : forall x: A, B x := by
  list_iff_ind
  hammer [] {}

namespace HammerCases.MissingIndDef
