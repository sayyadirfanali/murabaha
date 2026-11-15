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

def WellFormed (t : Terms) : Prop := t.schedule.sum = t.price

def behindCount (t : Terms) : List Nat → Nat
  | []      => 0
  | p :: ps => behindCount t ps + if p < t.scheduledTotal (ps.length + 1) then 1 else 0

def PriceInvariant (t : Terms) (s : State) : Prop :=
  s.bankReceived = s.pricePaid ∧ s.pricePaid ≤ t.price

structure PenaltyInvariant (t : Terms) (s : State) : Prop where
  priceInvariant : PriceInvariant t s
  length_eq : s.paidAtDueDates.length = s.dueDatesPassed
  charged_eq : s.penaltyCharged = t.latePenalty * behindCount t s.paidAtDueDates
  charity_full : 0 < s.charityReceived → s.pricePaid = t.price

theorem run_preserves {step : State → Event → Option State} {P : State → Prop}
    (hStep : ∀ {s e s'}, P s → step s e = some s' → P s') :
    ∀ {es s s'}, P s → run step s es = some s' → P s' := by
  intro es
  induction es with
  | nil => simp [run]
  | cons e es ih =>
    intro s s' hs hRun
    dsimp only [run] at hRun
    rcases hS : step s e with _ | ss
    · simp_all only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq]
    · simp_all only [Option.bind_eq_bind, Option.bind_some]
      exact ih (hStep hs hS) hRun

theorem scheduledTotal_le_price {t : Terms} (ht : WellFormed t) (k : Nat) :
    t.scheduledTotal k ≤ t.price := by
  unfold WellFormed at ht
  have := List.sum_take_add_sum_drop t.schedule k
  dsimp only [Terms.scheduledTotal]
  omega

theorem priceInvariant_init (t : Terms) : PriceInvariant t .init := by
  simp only [PriceInvariant, State.init, zero_le, and_self]

theorem penaltyInvariant_init (t : Terms) : PenaltyInvariant t .init := by
  dsimp only [State.init]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [PriceInvariant, zero_le, and_self]
  · simp only [List.length_nil]
  · simp only [behindCount, mul_zero]
  · simp only [lt_self_iff_false, IsEmpty.forall_iff]

theorem late_iff_behind {t : Terms} {s : State} (ht : WellFormed t)
    (hs : PenaltyInvariant t s) (k : Nat) :
    s.pricePaid < t.scheduledTotal k ↔ totalPaid s < t.scheduledTotal k := by
  unfold totalPaid
  have hBank := hs.priceInvariant.1
  have hPaid := hs.priceInvariant.2
  by_cases hc : s.charityReceived = 0
  · omega
  · have hFull := hs.charity_full (Nat.pos_of_ne_zero hc)
    have hLe := scheduledTotal_le_price ht k
    omega

theorem correct_priceInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : PriceInvariant t s) (h : contractCorrect t s e = some s') :
    PriceInvariant t s' := by
  obtain ⟨hBank, hPaid⟩ := hs
  dsimp only [PriceInvariant]
  cases e with
  | pay n =>
    dsimp only [contractCorrect] at h
    have hb := payPriceFirst_bankReceived h
    have hp := payPriceFirst_pricePaid h
    simp [priceRemaining] at *
    constructor <;> omega
  | dueDate =>
    dsimp only [contractCorrect] at h
    rw [passDueDate_bankReceived h, passDueDate_pricePaid h]
    exact ⟨hBank, hPaid⟩
  | settle =>
    dsimp only [contractCorrect] at h
    rw [settlePriceOnly_bankReceived h, settlePriceOnly_pricePaid h]
    simp [priceRemaining] at *
    omega

theorem correct_penaltyInvariant_step {t : Terms} {s s' : State} {e : Event}
    (ht : WellFormed t) (hs : PenaltyInvariant t s) (h : contractCorrect t s e = some s') :
    PenaltyInvariant t s' := by
  have hPrice := correct_priceInvariant_step hs.priceInvariant h
  obtain ⟨hBank, hPaid⟩ := hs.priceInvariant
  cases e with
  | pay n =>
    dsimp only [contractCorrect] at h
    refine ⟨hPrice, ?length_eq, ?charged_eq, ?charity_full⟩
    case length_eq =>
      rw [payPriceFirst_paidAtDueDates h, payPriceFirst_dueDatesPassed h]
      exact hs.length_eq
    case charged_eq =>
      rw [payPriceFirst_penaltyCharged h, payPriceFirst_paidAtDueDates h]
      exact hs.charged_eq
    case charity_full =>
      rw [payPriceFirst_charityReceived h, payPriceFirst_pricePaid h]
      dsimp only [priceRemaining]
      intro hPos
      rcases Nat.eq_zero_or_pos s.charityReceived with hc | hc
      · omega
      · have hFull := hs.charity_full hc
        omega
  | dueDate =>
    dsimp only [contractCorrect] at h
    refine ⟨hPrice, ?length_eq, ?charged_eq, ?charity_full⟩
    case length_eq =>
      rw [passDueDate_paidAtDueDates h, passDueDate_dueDatesPassed h,
        List.length_cons, hs.length_eq]
    case charged_eq =>
      rw [passDueDate_penaltyCharged h, passDueDate_paidAtDueDates h]
      simp only [behindCount, hs.length_eq]
      have key := late_iff_behind ht hs (s.dueDatesPassed + 1)
      by_cases hc : s.pricePaid < t.scheduledTotal (s.dueDatesPassed + 1)
      · have hc' := key.mp hc
        simp [hc, hc', hs.charged_eq, Nat.mul_add]
      · have hc' := mt key.mpr hc
        simp [hc, hc', hs.charged_eq]
    case charity_full =>
      rw [passDueDate_charityReceived h, passDueDate_pricePaid h]
      exact hs.charity_full
  | settle =>
    dsimp only [contractCorrect] at h
    refine ⟨hPrice, ?length_eq, ?charged_eq, ?charity_full⟩
    case length_eq =>
      rw [settlePriceOnly_paidAtDueDates h, settlePriceOnly_dueDatesPassed h]
      exact hs.length_eq
    case charged_eq =>
      rw [settlePriceOnly_penaltyCharged h, settlePriceOnly_paidAtDueDates h]
      exact hs.charged_eq
    case charity_full =>
      exact fun _ => settlePriceOnly_pricePaid h

theorem correct_bank_within_price {t : Terms} {es : List Event} {s : State}
    (hRun : run (contractCorrect t) .init es = some s) :
    s.bankReceived ≤ t.price := by
  obtain ⟨hBank, hPaid⟩ :=
    run_preserves correct_priceInvariant_step (priceInvariant_init t) hRun
  omega

theorem correct_fair_penalties {t : Terms} {es : List Event} {s : State}
    (ht : WellFormed t) (hRun : run (contractCorrect t) .init es = some s) :
    s.penaltyCharged ≤ t.latePenalty * behindCount t s.paidAtDueDates := by
  obtain ⟨-, -, hCharged, -⟩ :=
    run_preserves (correct_penaltyInvariant_step ht) (penaltyInvariant_init t) hRun
  exact Nat.le_of_eq hCharged

def OpenInvariant (t : Terms) (s : State) : Prop :=
  s.isSettled = false → PriceInvariant t s

theorem settleWithPenalty_openInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : OpenInvariant t s) (h : contractSettleWithPenalty t s e = some s') :
    OpenInvariant t s' := by
  intro hOpen
  cases e with
  | pay n =>
    dsimp only [contractSettleWithPenalty] at h
    rw [payPriceFirst_isSettled h] at hOpen
    exact correct_priceInvariant_step (e := .pay n) (hs hOpen) h
  | dueDate =>
    dsimp only [contractSettleWithPenalty] at h
    rw [passDueDate_isSettled h] at hOpen
    exact correct_priceInvariant_step (e := .dueDate) (hs hOpen) h
  | settle =>
    dsimp only [contractSettleWithPenalty] at h
    rw [settleWithPenalty_isSettled h] at hOpen
    simp at hOpen

theorem settleWithPenalty_bank_eq {t : Terms} {s s' : State}
    (hs : PriceInvariant t s) (h : settleWithPenalty t s = some s') :
    s'.bankReceived = t.price + s.penaltyOwed := by
  obtain ⟨hBank, hPaid⟩ := hs
  rw [settleWithPenalty_bankReceived h]
  dsimp only [priceRemaining]
  omega

theorem settleWithPenalty_exceeds_iff {t : Terms} {es : List Event} {s s' : State}
    (hRun : run (contractSettleWithPenalty t) .init es = some s)
    (h : contractSettleWithPenalty t s .settle = some s') :
    s'.bankReceived = t.price + s.penaltyOwed
    ∧ (t.price < s'.bankReceived ↔ 0 < s.penaltyOwed) := by
  dsimp only [contractSettleWithPenalty] at h
  have hInv : OpenInvariant t s :=
    run_preserves settleWithPenalty_openInvariant_step (fun _ => priceInvariant_init t) hRun
  have hEq := settleWithPenalty_bank_eq (hInv (settleWithPenalty_wasOpen h)) h
  exact ⟨hEq, by omega⟩

structure SettleFairInvariant (t : Terms) (s : State) : Prop where
  paid_le    : s.pricePaid ≤ t.price
  bank_ge    : s.pricePaid ≤ s.bankReceived
  open_exact : s.pricePaid < t.price → s.bankReceived = s.pricePaid ∧ s.charityReceived = 0
  length_eq  : s.paidAtDueDates.length = s.dueDatesPassed
  charged_eq : s.penaltyCharged = t.latePenalty * behindCount t s.paidAtDueDates

theorem settleFairInvariant_init (t : Terms) : SettleFairInvariant t .init := by
  dsimp only [State.init]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.zero_le _
  · exact le_refl _
  · intro _
    exact ⟨rfl, rfl⟩
  · simp only [List.length_nil]
  · simp only [behindCount, mul_zero]

theorem late_iff_behind_of {t : Terms} {s : State} (ht : WellFormed t)
    (hle : s.pricePaid ≤ t.price) (hge : s.pricePaid ≤ s.bankReceived)
    (hOpen : s.pricePaid < t.price → s.bankReceived = s.pricePaid ∧ s.charityReceived = 0)
    (k : Nat) :
    s.pricePaid < t.scheduledTotal k ↔ totalPaid s < t.scheduledTotal k := by
  unfold totalPaid
  have hS := scheduledTotal_le_price ht k
  by_cases hp : s.pricePaid < t.price
  · obtain ⟨hb, hc⟩ := hOpen hp
    omega
  · omega

theorem settleWithPenalty_fairInvariant_step {t : Terms} {s s' : State} {e : Event}
    (ht : WellFormed t) (hs : SettleFairInvariant t s)
    (h : contractSettleWithPenalty t s e = some s') :
    SettleFairInvariant t s' := by
  have hle := hs.paid_le
  have hge := hs.bank_ge
  cases e with
  | pay n =>
    dsimp only [contractSettleWithPenalty] at h
    have hp := payPriceFirst_pricePaid h
    have hb := payPriceFirst_bankReceived h
    have hc := payPriceFirst_charityReceived h
    dsimp only [priceRemaining] at hp hb hc
    refine ⟨?paid_le, ?bank_ge, ?open_exact, ?length_eq, ?charged_eq⟩
    case paid_le => omega
    case bank_ge => omega
    case open_exact =>
      intro hlt
      have hWasOpen : s.pricePaid < t.price := by omega
      obtain ⟨hb0, hc0⟩ := hs.open_exact hWasOpen
      omega
    case length_eq =>
      rw [payPriceFirst_paidAtDueDates h, payPriceFirst_dueDatesPassed h]
      exact hs.length_eq
    case charged_eq =>
      rw [payPriceFirst_penaltyCharged h, payPriceFirst_paidAtDueDates h]
      exact hs.charged_eq
  | dueDate =>
    dsimp only [contractSettleWithPenalty] at h
    refine ⟨?paid_le, ?bank_ge, ?open_exact, ?length_eq, ?charged_eq⟩
    case paid_le =>
      rw [passDueDate_pricePaid h]
      exact hle
    case bank_ge =>
      rw [passDueDate_pricePaid h, passDueDate_bankReceived h]
      exact hge
    case open_exact =>
      rw [passDueDate_pricePaid h, passDueDate_bankReceived h, passDueDate_charityReceived h]
      exact hs.open_exact
    case length_eq =>
      rw [passDueDate_paidAtDueDates h, passDueDate_dueDatesPassed h,
        List.length_cons, hs.length_eq]
    case charged_eq =>
      rw [passDueDate_penaltyCharged h, passDueDate_paidAtDueDates h]
      simp only [behindCount, hs.length_eq]
      have key := late_iff_behind_of ht hle hge hs.open_exact (s.dueDatesPassed + 1)
      by_cases hc : s.pricePaid < t.scheduledTotal (s.dueDatesPassed + 1)
      · have hc' := key.mp hc
        simp [hc, hc', hs.charged_eq, Nat.mul_add]
      · have hc' := mt key.mpr hc
        simp [hc, hc', hs.charged_eq]
  | settle =>
    dsimp only [contractSettleWithPenalty] at h
    have hb := settleWithPenalty_bankReceived h
    dsimp only [priceRemaining] at hb
    refine ⟨?paid_le, ?bank_ge, ?open_exact, ?length_eq, ?charged_eq⟩
    case paid_le =>
      rw [settleWithPenalty_pricePaid h]
    case bank_ge =>
      rw [settleWithPenalty_pricePaid h]
      omega
    case open_exact =>
      intro hlt
      rw [settleWithPenalty_pricePaid h] at hlt
      omega
    case length_eq =>
      rw [settleWithPenalty_paidAtDueDates h, settleWithPenalty_dueDatesPassed h]
      exact hs.length_eq
    case charged_eq =>
      rw [settleWithPenalty_penaltyCharged h, settleWithPenalty_paidAtDueDates h]
      exact hs.charged_eq

theorem settleWithPenalty_fair_penalties {t : Terms} {es : List Event} {s : State}
    (ht : WellFormed t) (hRun : run (contractSettleWithPenalty t) .init es = some s) :
    s.penaltyCharged ≤ t.latePenalty * behindCount t s.paidAtDueDates := by
  have hInv :=
    run_preserves (settleWithPenalty_fairInvariant_step ht) (settleFairInvariant_init t) hRun
  exact Nat.le_of_eq hInv.charged_eq

theorem penaltyFirst_priceInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : PriceInvariant t s) (h : contractPenaltyFirst t s e = some s') :
    PriceInvariant t s' := by
  cases e with
  | pay n =>
    dsimp only [contractPenaltyFirst] at h
    obtain ⟨hBank, hPaid⟩ := hs
    have hb := payPenaltyFirst_bankReceived h
    have hp := payPenaltyFirst_pricePaid h
    have hg := payPenaltyFirst_guard h
    dsimp only [PriceInvariant]
    dsimp only [priceRemaining] at hg
    constructor <;> omega
  | dueDate =>
    dsimp only [contractPenaltyFirst] at h
    exact correct_priceInvariant_step (e := .dueDate) hs h
  | settle =>
    dsimp only [contractPenaltyFirst] at h
    exact correct_priceInvariant_step (e := .settle) hs h

theorem penaltyFirst_bank_within_price {t : Terms} {es : List Event} {s : State}
    (hRun : run (contractPenaltyFirst t) .init es = some s) :
    s.bankReceived ≤ t.price := by
  obtain ⟨hBank, hPaid⟩ :=
    run_preserves penaltyFirst_priceInvariant_step (priceInvariant_init t) hRun
  omega

def dueByNext (t : Terms) (s : State) : Nat := t.scheduledTotal (s.dueDatesPassed + 1)

theorem penaltyFirst_undeserved_iff {t : Terms} {es : List Event} {s s' : State}
    (hPen : 0 < t.latePenalty)
    (hRun : run (contractPenaltyFirst t) .init es = some s)
    (h : contractPenaltyFirst t s .dueDate = some s') :
    (s.penaltyCharged < s'.penaltyCharged ∧ dueByNext t s ≤ totalPaid s) ↔
      (dueByNext t s ≤ totalPaid s ∧ totalPaid s < dueByNext t s + s.charityReceived) := by
  dsimp only [contractPenaltyFirst] at h
  obtain ⟨hBank, -⟩ :=
    run_preserves penaltyFirst_priceInvariant_step (priceInvariant_init t) hRun
  have hc := passDueDate_penaltyCharged h
  unfold totalPaid dueByNext
  by_cases hLate : s.pricePaid < t.scheduledTotal (s.dueDatesPassed + 1)
  · rw [ite_eq_left hLate] at hc
    omega
  · rw [ite_eq_right hLate] at hc
    omega

theorem penaltyFirst_unfair :
    ¬ ∀ es s, run (contractPenaltyFirst demo) .init es = some s →
      s.penaltyCharged ≤ demo.latePenalty * behindCount demo s.paidAtDueDates := by
  intro h
  have hBound := h latePayer _ rfl
  revert hBound
  decide

theorem settleWithPenalty_exceeds_price :
    ¬ ∀ es s, run (contractSettleWithPenalty demo) .init es = some s →
      s.bankReceived ≤ demo.price := by
  intro h
  have hBound := h earlySettler _ rfl
  revert hBound
  decide

end Murabaha
