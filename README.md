# Murabaha

A mathematical model of a simple **Murabaha** (cost-plus deferred sale) contract, checked by a computer proof assistant (Lean 4).

It proves two rules hold in a properly drafted Murabaha contract, and shows that changing a single payment or settlement clause breaks them.

A Murabaha is a Shariah-compliant sale on deferred payment. It follows specific trade rules rather than lending rules:

1. A bank buys goods first, takes ownership and risk, and then sells them to a buyer at cost plus an agreed **markup** (profit).
2. The total sale price (**cost** plus markup) is fixed when the contract is signed and cannot increase over time.
3. If the buyer pays late, a contract may require a **late-payment penalty** to deter default, but that money must go to charity—never to the bank as extra profit.

## Need

In a proper Murabaha, the bank's profit comes from a trade sale, so the price must not grow when a buyer is late, and any deterrent penalty belongs to charity rather than the bank.

However, when a contract is drafted by adapting standard banking templates, a clause that looks routine in a conventional loan can quietly break these Shariah rules when payments are late or settled early:

- **Payment allocation:** Conventional loan contracts often apply each payment first to fees and charges, and only then to the amount borrowed. Copied into a Murabaha, such a clause pays charity penalties before the sale price, causing later instalments to fall short.
- **Early settlement:** A standard payoff clause often requires the buyer to settle everything still owed under the agreement. In a Murabaha, if the bank collects every unpaid amount at settlement, penalties owed to charity end up with the bank.

Two real-world examples show how small wording differences around price, profit, and late charges create major problems:

- **Compounding Late Fees (USA):** Applying a new payment to old late fees before paying the scheduled instalment (which causes the new instalment to fall short and trigger another late fee) is a practice known as **pyramiding late fees**. It is banned in US consumer credit under the Federal Trade Commission's Credit Practices Rule (16 CFR Part 444). In 2016 a US appeals court held that a lender broke Maryland law in exactly this way: its loan note applied each payment "first to late charges, then to accrued interest, and then to the principal."
- **Earned vs Unearned Profit (Malaysia):** In *Affin Bank Bhd v Zulkifli bin Abdullah* (decided 2005), a buyer financed a house of about RM394,000 under a deferred-sale facility and defaulted after paying about RM33,000. The bank claimed the full deferred sale price of about RM959,000, which included profit for future years that had not yet elapsed. The High Court held that profit for unexpired tenure was unearned and reduced the bank's claim to about RM583,000.

This model covers the two clauses above. It does not cover the Malaysian issue, which concerns rebates of profit on early settlement.

Turning a clause into the model is done by hand: I read each clause, decided what it means, and wrote that meaning as a rule in Lean. The proof assistant then checks every consequence of those rules, but it does not check that I read the clause correctly. That step is open to review, and is the reason the rules are spelled out in plain words below.

## Findings

> "In a properly drafted Murabaha contract, the bank never receives more than the agreed sale price (cost plus markup), regardless of how many instalments are late or when the buyer settles."

> "In a properly drafted Murabaha contract, total penalties charged never exceed one penalty per due date on which the buyer's cumulative payments were actually behind schedule."

> "If a contract applies payments to unpaid penalties before the sale price, a single late instalment can trigger repeated penalties on every future due date, even when every later instalment is paid in full and on time."

> "If an early-settlement clause collects all unpaid balances into the bank's account, late penalties owed to charity end up with the bank."

The first two findings hold **universally**, i.e., for **every** sequence of payments, due dates, and early settlement that the contract accepts. The first holds for any contract terms. The second holds whenever the instalments add up to the sale price.

The last two findings are proved by showing specific, realistic payment sequences where the faulty contracts fail.

## Model

A contract's **terms** consist of three whole numbers and a list: the bank's purchase **cost**, the agreed **markup**, the fixed **late penalty** per missed due date, and a **schedule** listing the amount of each instalment.

The **price** is `cost + markup`.

Time moves from one scheduled **due date** to the next rather than by calendar days. Three types of **events** can occur in any order:

- **Payment (`pay n`)**: The buyer pays an amount `n` (greater than zero, and no more than the total unpaid price plus unpaid penalties).
- **Due date (`dueDate`)**: The next scheduled due date arrives. If the buyer has paid less toward the sale price than the schedule requires up to that date, one late penalty is added.
- **Early settlement (`settle`)**: The buyer closes the contract early (allowed once, provided the contract has not already been settled).

Any number of payments—or none—can happen between two due dates.

The **State** of the contract tracks the running totals as events happen: how many due dates have passed, whether the contract is settled, how much of the sale price is paid, how much penalty is currently owed, total penalties ever charged, total money received by the bank, total money received by charity, and a running record of total money paid at each past due date.

The model formalises three versions (one proper, two faulty) of the contract:

| Version | Where payment goes first | What early settlement collects |
|---|---|---|
| `contractCorrect` | Unpaid sale price (remainder to charity penalties) | Unpaid sale price only |
| `contractPenaltyFirst` | Unpaid charity penalties (remainder to sale price) | Unpaid sale price only |
| `contractSettleWithPenalty` | Unpaid sale price (remainder to charity penalties) | Unpaid sale price *plus* unpaid penalties (all to the bank) |

## Example

Suppose a bank buys an item for **100** and sells it for **112** (markup of **12**), payable in four instalments of **28**, with a late penalty of **2** per missed due date.

### Cascading Penalties (`contractPenaltyFirst`)

Suppose the buyer misses the first due date, pays double (**56**) before the second due date, pays **28** on time before the third and fourth due dates, and finally pays **2** more.

In both contracts below, the buyer hands over **114** in total. What differs is how the contract splits it.

**Proper contract (`contractCorrect`)**

| Due date | Cumulative cash paid | Schedule requires | Applied to sale price | Behind schedule? | Penalty charged |
|---|---|---|---|---|---|
| 1 | 0 | 28 | 0 | Yes | 2 |
| 2 | 56 | 56 | 56 | No | 0 |
| 3 | 84 | 84 | 84 | No | 0 |
| 4 | 112 | 112 | 112 | No | 0 |

After the fourth due date, the final payment of **2** clears the single charity penalty. The bank receives **112**, charity receives **2**, and total penalties charged are **2**.

**Penalty-first contract (`contractPenaltyFirst`)**

| Due date | Cumulative cash paid | Schedule requires | Applied to sale price | Behind schedule? | Penalty charged |
|---|---|---|---|---|---|
| 1 | 0 | 28 | 0 | Yes | 2 |
| 2 | 56 | 56 | 54 | No | 2 |
| 3 | 84 | 84 | 80 | No | 2 |
| 4 | 112 | 112 | 106 | No | 2 |

Because each payment pays off the prior penalty first, the amount credited toward the sale price is always short by 2, triggering a fresh penalty at every single due date. After the final payment of **2**, total penalties charged reach **8** (all paid to charity), leaving **6** of the sale price still unpaid—even though the buyer was behind schedule only once.

### Absorbing Charity (`contractSettleWithPenalty`)

Using the same terms (price **112**, four instalments of **28**, penalty **2**), suppose the buyer misses the first due date (incurring a penalty of **2**), pays **56** before the second due date, and then settles early once the second due date has passed:

- Under **`contractCorrect`**, early settlement collects only the remaining unpaid price (**56**). The bank receives **112** in total, and the **2** penalty remains owed to charity.

- Under **`contractSettleWithPenalty`**, early settlement collects both the unpaid price (**56**) and the unpaid penalty (**2**) for the bank. The bank receives **114**—**2** above the fixed contract price—and charity receives **0**.

## Theorems

Each formal result in `Murabaha.lean` is checked automatically by Lean 4:

| Theorem | Meaning |
|---|---|
| `correct_bank_within_price` | In `contractCorrect`, the total money received by the bank never exceeds the contract price (`cost + markup`). |
| `correct_fair_penalties` | Provided the instalment schedule adds up to the contract price (`WellFormed`), total penalties charged in `contractCorrect` never exceed the late penalty multiplied by the number of due dates on which the buyer's total payments were behind schedule. |
| `penaltyFirst_unfair` | In `contractPenaltyFirst`, total penalties charged can exceed that fair limit (proved using the cascading-penalty example above). |
| `settleWithPenalty_exceeds_price` | In `contractSettleWithPenalty`, the bank can receive more than the contract price (proved using the early-settlement example above). |

A buyer is defined as **behind** at a due date if the total cash paid by that date (to the bank and charity combined) is less than the cumulative amount required by the schedule up to that date. Because this definition depends only on total cash paid, it treats all three contract versions identically.

To prove `correct_fair_penalties` for every possible sequence of events, the proof establishes a **state invariant**—a set of conditions that is true when the contract starts and remains true after every single event. The crucial condition is that in `contractCorrect`, charity never receives a single unit of payment until the sale price is paid in full. Consequently, while the price is still being paid off, "price paid so far" and "total cash paid so far" are always identical, so a buyer is marked late if and only if they are genuinely behind schedule.

## Scope and limitations

This model covers only post-sale payment and penalty allocation. It leaves out pre-sale trade requirements (asset purchase, possession, risk, and cost disclosure), early-settlement profit rebates (*Ibra'*), differing scholarly positions on late penalties (such as prohibiting penalties altogether or compensating actual loss), exact calendar dates, and currency subunits.

In addition, `settle` collects only the unpaid price without forcing immediate payment of leftover charity penalties (which can still be paid after `settle`), and the two failure theorems show specific examples of failure rather than proving failure for every contract.

The definition of **behind** reads the buyer's total payments from the bank's and charity's running totals. This assumes every payment ends up with one of the two. That is true of all three contract versions here, but it is not checked as a separate theorem.

The rules modelled here reflect my reading of the sources below and have not yet been reviewed by a Shariah scholar. Corrections and critique are welcome.

## Building

This project uses Lean 4 and Mathlib. To download pre-built Mathlib files and verify all proofs locally:

```bash
lake exe cache get
lake build
```

## Sources

- **AAOIFI**, *Shari'ah Standard No. 8: Murabahah* (Accounting and Auditing Organization for Islamic Financial Institutions).
- **OIC International Islamic Fiqh Academy**, *Resolution No. 40–41 (2/5 & 3/5)*, 5th Session, Kuwait, 1988 (on binding promises and Murabaha to the purchase orderer).
- ***Affin Bank Bhd v Zulkifli bin Abdullah*** [2006] 3 MLJ 67, High Court, Kuala Lumpur (decided 29 December 2005).
- **US Federal Trade Commission**, *Credit Practices Rule*, 16 CFR Part 444 (prohibiting pyramiding of late charges).

## Authorship

I designed the contract model, chose the Shariah properties and invariants to verify, and wrote many of the proofs.

Claude wrote the initial Lean definitions, suggested strengthening the state invariant, completed several proof steps, and drafted the first version of this README.

Gemini edited and tightened this README for clarity, structure, and plain-English presentation.

I have personally reviewed every definition and proof in the Lean file and verified that they match the claims stated here.

## Contact

Irfan Ali | [irfanali.org](https://irfanali.org)

Corrections are welcome, especially regarding my reading of the statutes.

Please open an issue on GitHub or email me.


## Licence

MIT