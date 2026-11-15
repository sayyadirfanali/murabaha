# Murabaha

**Lean 4** formalisation of a **Murabaha** (cost-plus deferred sale) contract.

It shows how a Murabaha's payment rules can be stated as machine-checked invariants (rules that hold after every event). A carefully drafted Murabaha contract provably satisfies those invariants, while changing a single clause can break them.

## The Problem

In a Murabaha, a bank buys an asset, assumes ownership risk, and resells it to a buyer on deferred payment at `cost + markup`. Two rules govern post-sale payments:

1. **Fixed price:** The total sale price is fixed at signing and cannot grow if the buyer pays late.
2. **Charity-only penalties:** Any late-payment penalty charged to deter default must go to charity, never to the bank as extra revenue.

When Murabaha agreements are drafted by adapting conventional loan templates, routine boilerplate can quietly violate these rules:

- **Payment allocation (pyramiding penalties):** Conventional loan notes often apply payments to late fees before principal, leading to "pyramided" late fees prohibited under the FTC Credit Practices Rule (16 CFR Part 444). Copied into a Murabaha, this causes later instalments to fall short and trigger cascading penalties.
- **Early settlement:** Standard payoff clauses often sweep all unpaid balances into the lender's account. In a Murabaha, collecting unpaid penalties at settlement transfers charity funds to the bank.

Formalising these clauses in Lean 4 separates the **logical deduction** (verified mechanically from the state transitions) from the **legal interpretation** of the clauses (documented under Scope and Limitations).

## Results

| Variant | Penalties are fair | Bank receives at most the price |
|---|---|---|
| `contractCorrect` | ✓ | ✓ |
| `contractPenaltyFirst` | ✗ | ✓ |
| `contractSettleWithPenalty` | ✓ | ✗ |

Each faulty variant fails exactly one check, so a reviewer who checks only one rule misses one of the faults.

## Model

The definitions are in `Murabaha/Model.lean`.

A contract's `Terms` consist of three natural numbers and a list: `cost`, `markup` (with `price = cost + markup`), a fixed per-default `latePenalty`, and an instalment `schedule` (in a `WellFormed` contract, `schedule.sum = price`).

Time advances by scheduled due dates rather than calendar days. Three events can occur in any order, each accepted only when it makes sense:

- `pay n`: The buyer pays `n > 0` (up to total unpaid price plus unpaid penalties).
- `dueDate`: The next due date arrives (up to `schedule.length`); if cumulative payments toward the sale price (`pricePaid`) are below the schedule requirement to date, one `latePenalty` is added.
- `settle`: The buyer closes the contract early (allowed once, when `isSettled = false`).

The contract `State` tracks due dates elapsed, settlement status, price paid, penalties owed, total penalties charged, cumulative cash received by the bank and by charity, and cumulative cash paid at each past due date.

The model compares three contract variants:

| Variant | Payment allocation priority | Early settlement collects |
|---|---|---|
| `contractCorrect` | Unpaid sale price first (remainder to charity penalties) | Unpaid sale price only |
| `contractPenaltyFirst` | Unpaid charity penalties first (remainder to sale price) | Unpaid sale price only |
| `contractSettleWithPenalty` | Unpaid sale price first (remainder to charity penalties) | Unpaid sale price *plus* unpaid penalties (all to the bank) |

## Worked Examples

Suppose `cost = 100` and `markup = 12` (`price = 112`), payable in four instalments of **28**, with `latePenalty = 2` per missed due date (`demo`).

### 1. Cascading Penalties (`latePayer`)

The buyer misses due date 1, catches up by paying **56** (two payments of 28) before due date 2, pays **28** on time before due dates 3 and 4, and makes a final payment of **2** (**114** paid in total):

| Due date | Cash paid (Scheduled) | `contractCorrect` price paid (Penalty) | `contractPenaltyFirst` price paid (Penalty) |
|---:|---:|---:|---:|
| 1 | 0 (28) | 0 (**+2**) | 0 (**+2**) |
| 2 | 56 (56) | 56 (0) | 54 (**+2**) |
| 3 | 84 (84) | 84 (0) | 80 (**+2**) |
| 4 | 112 (112) | 112 (0) | 106 (**+2**) |

After the final payment of **2**:
- **`contractCorrect`:** Bank receives **112**, charity receives **2**, contract is fully paid.
- **`contractPenaltyFirst`:** Diverting **2** to charity before due date 2 leaves the sale price chronically short, triggering a fresh penalty at every subsequent due date. Total penalties reach **8** (all to charity), leaving **6** of the sale price unpaid despite the buyer being behind schedule only once.

### 2. Absorbing Charity (`earlySettler`)

The buyer misses due date 1 (incurring a penalty of **2**), pays **56** before due date 2, and settles early after due date 2 passes:
- **`contractCorrect`:** Settlement collects only the unpaid sale price (**56**). The bank receives **112** in total, and **2** remains owed to charity.
- **`contractSettleWithPenalty`:** Settlement sweeps both the unpaid price (**56**) and unpaid penalty (**2**) into the bank's account. The bank receives **114** (**2** above the fixed contract price) and charity receives **0**.

## Formalised Theorems (`Murabaha/Theorems.lean`)

| Theorem | What It Proves |
|---|---|
| `correct_bank_within_price` | In `contractCorrect`, total cash received by the bank never exceeds `cost + markup` for any valid event sequence. |
| `correct_fair_penalties` | Provided `WellFormed`, total penalties charged in `contractCorrect` never exceed `latePenalty` times the number of due dates on which total cash paid was behind schedule. |
| `penaltyFirst_unfair` | In `contractPenaltyFirst`, total penalties charged can exceed that fair limit (proved via `latePayer`). |
| `penaltyFirst_undeserved_iff` | Given `latePenalty > 0`, an on-track buyer in `contractPenaltyFirst` is charged a penalty at a due date if and only if total cash paid covers the schedule requirement, but falls short once cumulative charity payments are deducted. |
| `penaltyFirst_bank_within_price` | `contractPenaltyFirst` still keeps total cash received by the bank within `cost + markup`. |
| `settleWithPenalty_exceeds_price` | In `contractSettleWithPenalty`, the bank can receive more than `cost + markup` (proved via `earlySettler`). |
| `settleWithPenalty_exceeds_iff` | In `contractSettleWithPenalty`, settlement leaves the bank with `price + penaltyOwed`, exceeding `price` if and only if `penaltyOwed > 0`. |
| `settleWithPenalty_fair_penalties` | Provided `WellFormed`, `contractSettleWithPenalty` still satisfies the fair-penalty bound. |

A buyer is defined as **behind** at a due date if total cash paid (`bankReceived + charityReceived`) is below the cumulative schedule requirement—a definition independent of internal allocation rules. `correct_fair_penalties` is proved via a state invariant showing that in `contractCorrect`, charity receives nothing until the sale price is paid in full; while the price is unpaid, `pricePaid` equals `totalPaid`.

## Scope and Limitations

- Models post-sale payments only: no asset acquisition, *Ibra'* rebates, day-counts, or currency subunits.
- Assumes charity-directed late penalties are permitted; stricter views (e.g. OIC Fiqh Academy Resolution 51 (2/6)) are not modelled.
- Calling `settle` requires only `isSettled = false`.
- After `settle`, `dueDate` events and payments toward unpaid charity penalties are still allowed.
- `totalPaid` is read directly from `bankReceived + charityReceived`.
- Reflects the author's reading of the sources below and has not yet been reviewed by a Shariah scholar.

## Usage

```bash
lake exe cache get && lake build
```

## Sources

- **AAOIFI**, *Shari'ah Standard No. 8: Murabahah*.
- **AAOIFI**, *Shari'ah Standard No. 3: Procrastinating Debtor*.
- **OIC Fiqh Academy**, *Resolution No. 51 (2/6) on Instalment Sale*, Jeddah, 1990.
- **US FTC**, *Credit Practices Rule*, 16 CFR Part 444.

## Authorship

I designed the contract model, chose the properties and invariants to verify, and wrote the run preservation and invariance proofs. Claude and Gemini assisted with invariant strengthening, proof structuring, README drafting. I have reviewed all definitions and theorem statements against the claims stated here.

## Contact

Irfan Ali | [irfanali.org](https://irfanali.org)

Corrections and critique are welcome, especially regarding the Shariah rules and formalisation. Please open an issue on GitHub or email me.
