import Mathlib.Tactic

namespace Murabaha

structure Terms where
  cost : Nat
  markup : Nat
  schedule : List Nat
  latePenalty : Nat
  deriving Repr

def Terms.price (t : Terms) : Nat := t.cost + t.markup

def Terms.scheduledTotal (t : Terms) (k : Nat) : Nat := (t.schedule.take k).sum

inductive Event where
  | pay (amount : Nat)
  | settle
  | dueDate
  deriving Repr, DecidableEq

structure State where
  dueDatesPassed : Nat := 0       -- due dates passed so far
  isSettled : Bool := false       -- is contract settled via early payment
  pricePaid : Nat := 0            -- part of the price paid so far
  penaltyOwed : Nat := 0          -- penalty charged but not yet paid
  penaltyCharged : Nat := 0       -- all penalty ever charged
  bankReceived : Nat := 0         -- all money received by the bank
  charityReceived : Nat := 0      -- all money received by charity
  paidAtDueDates : List Nat := [] -- ghost total paid at each due date newest first
  deriving Repr

def State.init : State := {}

def priceRemaining (t : Terms) (s : State) : Nat := t.price - s.pricePaid

def totalPaid (s : State) : Nat := s.bankReceived + s.charityReceived

def passDueDate (t : Terms) (s : State) : Option State :=
  if s.dueDatesPassed ≥ t.schedule.length then none else
  let isLate := decide (s.pricePaid < t.scheduledTotal (s.dueDatesPassed + 1))
  let charge := if isLate then t.latePenalty else 0
  some { s with dueDatesPassed := s.dueDatesPassed + 1
                penaltyOwed := s.penaltyOwed + charge
                penaltyCharged := s.penaltyCharged + charge
                paidAtDueDates := totalPaid s :: s.paidAtDueDates }

theorem passDueDate_dueDatesPassed {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.dueDatesPassed = s.dueDatesPassed + 1 := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem passDueDate_pricePaid {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.pricePaid = s.pricePaid := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem passDueDate_penaltyCharged {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.penaltyCharged = s.penaltyCharged +
      (if s.pricePaid < t.scheduledTotal (s.dueDatesPassed + 1) then t.latePenalty else 0) := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp

theorem passDueDate_bankReceived {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.bankReceived = s.bankReceived := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem passDueDate_charityReceived {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.charityReceived = s.charityReceived := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp

theorem passDueDate_paidAtDueDates {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.paidAtDueDates = totalPaid s :: s.paidAtDueDates := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp

theorem passDueDate_isSettled {t : Terms} {s s' : State}
    (h : passDueDate t s = some s') :
    s'.isSettled = s.isSettled := by
  simp only [passDueDate, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

def payPriceFirst (t : Terms) (s : State) (n : Nat) : Option State :=
  if n = 0 ∨ n > priceRemaining t s + s.penaltyOwed then none else
  let toPrice := min n (priceRemaining t s)
  let toPenalty := n - toPrice
  some { s with pricePaid := s.pricePaid + toPrice
                bankReceived := s.bankReceived + toPrice
                penaltyOwed := s.penaltyOwed - toPenalty
                charityReceived := s.charityReceived + toPenalty }

theorem payPriceFirst_dueDatesPassed {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.dueDatesPassed = s.dueDatesPassed := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_pricePaid {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.pricePaid = s.pricePaid + min n (priceRemaining t s) := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_penaltyCharged {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.penaltyCharged = s.penaltyCharged := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_bankReceived {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.bankReceived = s.bankReceived + min n (priceRemaining t s) := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_charityReceived {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.charityReceived = s.charityReceived + (n - min n (priceRemaining t s)) := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_paidAtDueDates {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.paidAtDueDates = s.paidAtDueDates := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPriceFirst_isSettled {t : Terms} {s s' : State} {n : Nat}
    (h : payPriceFirst t s n = some s') :
    s'.isSettled = s.isSettled := by
  simp only [payPriceFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

def payPenaltyFirst (t : Terms) (s : State) (n : Nat) : Option State :=
  if n = 0 ∨ n > priceRemaining t s + s.penaltyOwed then none else
  let toPenalty := min n s.penaltyOwed
  let toPrice := n - toPenalty
  some { s with pricePaid := s.pricePaid + toPrice
                bankReceived := s.bankReceived + toPrice
                penaltyOwed := s.penaltyOwed - toPenalty
                charityReceived := s.charityReceived + toPenalty }

theorem payPenaltyFirst_pricePaid {t : Terms} {s s' : State} {n : Nat}
    (h : payPenaltyFirst t s n = some s') :
    s'.pricePaid = s.pricePaid + (n - min n s.penaltyOwed) := by
  simp only [payPenaltyFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  simp

theorem payPenaltyFirst_bankReceived {t : Terms} {s s' : State} {n : Nat}
    (h : payPenaltyFirst t s n = some s') :
    s'.bankReceived = s.bankReceived + (n - min n s.penaltyOwed) := by
  simp only [payPenaltyFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem payPenaltyFirst_guard {t : Terms} {s s' : State} {n : Nat}
    (h : payPenaltyFirst t s n = some s') :
    n ≤ priceRemaining t s + s.penaltyOwed := by
  simp only [payPenaltyFirst,
    gt_iff_lt, Option.ite_none_left_eq_some, not_or, not_lt, Option.some.injEq] at h
  obtain ⟨⟨-, hLe⟩, -⟩ := h
  exact hLe

def settlePriceOnly (t : Terms) (s : State) : Option State :=
  if s.isSettled then none else
  some { s with isSettled := true
                pricePaid := t.price
                bankReceived := s.bankReceived + priceRemaining t s }

theorem settlePriceOnly_dueDatesPassed {t : Terms} {s s' : State}
    (h : settlePriceOnly t s = some s') :
    s'.dueDatesPassed = s.dueDatesPassed := by
  simp only [settlePriceOnly, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settlePriceOnly_pricePaid {t : Terms} {s s' : State}
    (h : settlePriceOnly t s = some s') :
    s'.pricePaid = t.price := by
  simp only [settlePriceOnly, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settlePriceOnly_penaltyCharged {t : Terms} {s s' : State}
    (h : settlePriceOnly t s = some s') :
    s'.penaltyCharged = s.penaltyCharged := by
  simp only [settlePriceOnly, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settlePriceOnly_bankReceived {t : Terms} {s s' : State}
    (h : settlePriceOnly t s = some s') :
    s'.bankReceived = s.bankReceived + priceRemaining t s := by
  simp only [settlePriceOnly, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settlePriceOnly_paidAtDueDates {t : Terms} {s s' : State}
    (h : settlePriceOnly t s = some s') :
    s'.paidAtDueDates = s.paidAtDueDates := by
  simp only [settlePriceOnly, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

def settleWithPenalty (t : Terms) (s : State) : Option State :=
  if s.isSettled then none else
  some { s with isSettled := true
                pricePaid := t.price
                penaltyOwed := 0
                bankReceived := s.bankReceived + priceRemaining t s + s.penaltyOwed }

theorem settleWithPenalty_wasOpen {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s.isSettled = false := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨hOpen, -⟩ := h
  simpa using hOpen

theorem settleWithPenalty_isSettled {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.isSettled = true := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settleWithPenalty_bankReceived {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.bankReceived = s.bankReceived + priceRemaining t s + s.penaltyOwed := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settleWithPenalty_dueDatesPassed {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.dueDatesPassed = s.dueDatesPassed := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settleWithPenalty_pricePaid {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.pricePaid = t.price := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settleWithPenalty_penaltyCharged {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.penaltyCharged = s.penaltyCharged := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem settleWithPenalty_paidAtDueDates {t : Terms} {s s' : State}
    (h : settleWithPenalty t s = some s') :
    s'.paidAtDueDates = s.paidAtDueDates := by
  simp only [settleWithPenalty, Option.ite_none_left_eq_some, Option.some.injEq] at h
  obtain ⟨-, rfl⟩ := h
  rfl

def contractCorrect (t : Terms) (s : State) : Event → Option State
  | .pay n   => payPriceFirst t s n
  | .dueDate => passDueDate t s
  | .settle  => settlePriceOnly t s

def contractPenaltyFirst (t : Terms) (s : State) : Event → Option State
  | .pay n   => payPenaltyFirst t s n
  | .dueDate => passDueDate t s
  | .settle  => settlePriceOnly t s

def contractSettleWithPenalty (t : Terms) (s : State) : Event → Option State
  | .pay n   => payPriceFirst t s n
  | .dueDate => passDueDate t s
  | .settle  => settleWithPenalty t s

def run (step : State → Event → Option State) : State → List Event → Option State
  | s, []      => some s
  | s, e :: es => step s e >>= fun s' => run step s' es

def demo : Terms :=
  { cost := 100, markup := 12, latePenalty := 2, schedule := [28, 28, 28, 28] }

def latePayer : List Event :=
  [.dueDate, .pay 28, .pay 28, .dueDate, .pay 28, .dueDate, .pay 28, .dueDate, .pay 2]

def earlySettler : List Event :=
  [.dueDate, .pay 28, .pay 28, .dueDate, .settle]

def summary (s : State) : Nat × Nat × Nat × Nat :=
  (s.penaltyCharged, s.bankReceived, s.charityReceived, s.penaltyOwed)

#eval (run (contractCorrect           demo) .init latePayer).map summary     -- some (2, 112, 2, 0)
#eval (run (contractPenaltyFirst      demo) .init latePayer).map summary     -- some (8, 106, 8, 0)
#eval (run (contractCorrect           demo) .init earlySettler).map summary  -- some (2, 112, 0, 2)
#eval (run (contractSettleWithPenalty demo) .init earlySettler).map summary  -- some (2, 114, 0, 0)

end Murabaha
