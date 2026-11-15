import Murabaha.Model

namespace Murabaha

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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [State.init, PriceInvariant, behindCount]

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

theorem late_iff_behind {t : Terms} {s : State} (ht : WellFormed t)
    (hs : PenaltyInvariant t s) (k : Nat) :
    s.pricePaid < t.scheduledTotal k ↔ totalPaid s < t.scheduledTotal k :=
  late_iff_behind_of ht hs.priceInvariant.2 hs.priceInvariant.1.ge
    (fun hlt => ⟨hs.priceInvariant.1, by
      by_contra hc
      exact absurd (hs.charity_full (Nat.pos_of_ne_zero hc)) hlt.ne⟩) k

theorem correct_priceInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : PriceInvariant t s) (h : contractCorrect t s e = some s') :
    PriceInvariant t s' := by
  obtain ⟨hBank, hPaid⟩ := hs
  dsimp only [PriceInvariant]
  cases e <;> dsimp only [contractCorrect] at h
  case pay n =>
    have hb := payPriceFirst_bankReceived h
    have hp := payPriceFirst_pricePaid h
    simp only [priceRemaining] at hb hp
    constructor <;> omega
  case dueDate =>
    rw [passDueDate_bankReceived h, passDueDate_pricePaid h]
    exact ⟨hBank, hPaid⟩
  case settle =>
    rw [settlePriceOnly_bankReceived h, settlePriceOnly_pricePaid h]
    simp only [priceRemaining]
    constructor <;> omega

theorem correct_penaltyInvariant_step {t : Terms} {s s' : State} {e : Event}
    (ht : WellFormed t) (hs : PenaltyInvariant t s) (h : contractCorrect t s e = some s') :
    PenaltyInvariant t s' := by
  have hPrice := correct_priceInvariant_step hs.priceInvariant h
  have hPaid := hs.priceInvariant.2
  cases e <;> dsimp only [contractCorrect] at h
  case pay n =>
    refine ⟨hPrice, ?_, ?_, ?_⟩
    · rw [payPriceFirst_paidAtDueDates h, payPriceFirst_dueDatesPassed h, hs.length_eq]
    · rw [payPriceFirst_penaltyCharged h, payPriceFirst_paidAtDueDates h, hs.charged_eq]
    · rw [payPriceFirst_charityReceived h, payPriceFirst_pricePaid h]
      dsimp only [priceRemaining]
      intro hPos
      rcases Nat.eq_zero_or_pos s.charityReceived with hc | hc
      · omega
      · have := hs.charity_full hc
        omega
  case dueDate =>
    refine ⟨hPrice, ?_, ?_, ?_⟩
    · rw [passDueDate_paidAtDueDates h, passDueDate_dueDatesPassed h,
        List.length_cons, hs.length_eq]
    · rw [passDueDate_penaltyCharged h, passDueDate_paidAtDueDates h, hs.charged_eq]
      simp only [behindCount, hs.length_eq, late_iff_behind ht hs]
      split_ifs <;> ring
    · rw [passDueDate_charityReceived h, passDueDate_pricePaid h]
      exact hs.charity_full
  case settle =>
    refine ⟨hPrice, ?_, ?_, fun _ => settlePriceOnly_pricePaid h⟩
    · rw [settlePriceOnly_paidAtDueDates h, settlePriceOnly_dueDatesPassed h, hs.length_eq]
    · rw [settlePriceOnly_penaltyCharged h, settlePriceOnly_paidAtDueDates h, hs.charged_eq]

theorem correct_bank_within_price {t : Terms} {es : List Event} {s : State}
    (hRun : run (contractCorrect t) .init es = some s) :
    s.bankReceived ≤ t.price := by
  obtain ⟨hBank, hPaid⟩ :=
    run_preserves correct_priceInvariant_step (priceInvariant_init t) hRun
  omega

theorem correct_fair_penalties {t : Terms} {es : List Event} {s : State}
    (ht : WellFormed t) (hRun : run (contractCorrect t) .init es = some s) :
    s.penaltyCharged ≤ t.latePenalty * behindCount t s.paidAtDueDates :=
  (run_preserves (correct_penaltyInvariant_step ht) (penaltyInvariant_init t) hRun).charged_eq.le

def OpenInvariant (t : Terms) (s : State) : Prop :=
  s.isSettled = false → PriceInvariant t s

theorem settleWithPenalty_openInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : OpenInvariant t s) (h : contractSettleWithPenalty t s e = some s') :
    OpenInvariant t s' := by
  intro hOpen
  cases e <;> dsimp only [contractSettleWithPenalty] at h
  case pay n =>
    rw [payPriceFirst_isSettled h] at hOpen
    exact correct_priceInvariant_step (e := .pay n) (hs hOpen) h
  case dueDate =>
    rw [passDueDate_isSettled h] at hOpen
    exact correct_priceInvariant_step (e := .dueDate) (hs hOpen) h
  case settle =>
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.init, behindCount]

theorem settleWithPenalty_fairInvariant_step {t : Terms} {s s' : State} {e : Event}
    (ht : WellFormed t) (hs : SettleFairInvariant t s)
    (h : contractSettleWithPenalty t s e = some s') :
    SettleFairInvariant t s' := by
  have hle := hs.paid_le
  have hge := hs.bank_ge
  cases e <;> dsimp only [contractSettleWithPenalty] at h
  case pay n =>
    have hp := payPriceFirst_pricePaid h
    have hb := payPriceFirst_bankReceived h
    have hc := payPriceFirst_charityReceived h
    dsimp only [priceRemaining] at hp hb hc
    refine ⟨by omega, by omega, fun hlt => ?_, ?_, ?_⟩
    · obtain ⟨hb0, hc0⟩ := hs.open_exact (by omega)
      omega
    · rw [payPriceFirst_paidAtDueDates h, payPriceFirst_dueDatesPassed h, hs.length_eq]
    · rw [payPriceFirst_penaltyCharged h, payPriceFirst_paidAtDueDates h, hs.charged_eq]
  case dueDate =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [passDueDate_pricePaid h]
      exact hle
    · rw [passDueDate_pricePaid h, passDueDate_bankReceived h]
      exact hge
    · rw [passDueDate_pricePaid h, passDueDate_bankReceived h, passDueDate_charityReceived h]
      exact hs.open_exact
    · rw [passDueDate_paidAtDueDates h, passDueDate_dueDatesPassed h,
        List.length_cons, hs.length_eq]
    · rw [passDueDate_penaltyCharged h, passDueDate_paidAtDueDates h, hs.charged_eq]
      simp only [behindCount, hs.length_eq, late_iff_behind_of ht hle hge hs.open_exact]
      split_ifs <;> ring
  case settle =>
    have hb := settleWithPenalty_bankReceived h
    have hp := settleWithPenalty_pricePaid h
    dsimp only [priceRemaining] at hb
    refine ⟨by omega, by omega, fun hlt => absurd hlt (by omega), ?_, ?_⟩
    · rw [settleWithPenalty_paidAtDueDates h, settleWithPenalty_dueDatesPassed h, hs.length_eq]
    · rw [settleWithPenalty_penaltyCharged h, settleWithPenalty_paidAtDueDates h, hs.charged_eq]

theorem settleWithPenalty_fair_penalties {t : Terms} {es : List Event} {s : State}
    (ht : WellFormed t) (hRun : run (contractSettleWithPenalty t) .init es = some s) :
    s.penaltyCharged ≤ t.latePenalty * behindCount t s.paidAtDueDates :=
  (run_preserves (settleWithPenalty_fairInvariant_step ht) (settleFairInvariant_init t)
    hRun).charged_eq.le

theorem penaltyFirst_priceInvariant_step {t : Terms} {s s' : State} {e : Event}
    (hs : PriceInvariant t s) (h : contractPenaltyFirst t s e = some s') :
    PriceInvariant t s' := by
  cases e <;> dsimp only [contractPenaltyFirst] at h
  case pay n =>
    obtain ⟨hBank, hPaid⟩ := hs
    have hb := payPenaltyFirst_bankReceived h
    have hp := payPenaltyFirst_pricePaid h
    have hg := payPenaltyFirst_guard h
    dsimp only [PriceInvariant]
    dsimp only [priceRemaining] at hg
    constructor <;> omega
  case dueDate => exact correct_priceInvariant_step (e := .dueDate) hs h
  case settle => exact correct_priceInvariant_step (e := .settle) hs h

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
  split_ifs at hc <;> omega

theorem penaltyFirst_unfair :
    ¬ ∀ es s, run (contractPenaltyFirst demo) .init es = some s →
      s.penaltyCharged ≤ demo.latePenalty * behindCount demo s.paidAtDueDates :=
  fun h => absurd (h latePayer _ rfl) (by decide)

theorem settleWithPenalty_exceeds_price :
    ¬ ∀ es s, run (contractSettleWithPenalty demo) .init es = some s →
      s.bankReceived ≤ demo.price :=
  fun h => absurd (h earlySettler _ rfl) (by decide)

end Murabaha
