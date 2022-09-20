import Approx.Dyadic

structure Interval where
  lb : Dyadic
  ub : Dyadic
  lb_le_ub : lb ≤ ub
  deriving DecidableEq

instance : Membership Dyadic Interval where
  mem x i := i.lb ≤ x ∧ x ≤ i.ub

def Interval.add (i₁ i₂ : Interval) : Interval where
  lb := i₁.lb + i₂.lb
  ub := i₁.ub + i₂.ub
  lb_le_ub := sorry
