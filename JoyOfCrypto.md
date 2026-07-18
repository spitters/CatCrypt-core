# The Joy of Cryptography in CatCrypt — a roadmap

A plan for growing CatCrypt-core into a mechanized companion to Mike Rosulek's
free textbook *[The Joy of Cryptography](https://joyofcryptography.com/)*.

**Why this book.** Rosulek teaches with *interchangeable libraries*: a proof
replaces one library by an indistinguishable one, simplifies the composed code,
and repeats. That is exactly the state-separating-packages framework CatCrypt is
built on, and the "simplify the composed code" step is what the new tactics
(`ssprove_code_simpl`, `ssprove_contract_*`, `ssprove_copy_propagate_*`,
`ssprove_crypto`) automate. The book is therefore the natural showcase curriculum
— and, unusually, most of it is already formalized in the wider CatCrypt tree.

**How to read this roadmap.** It is aspirational, not a contract. Where we
already have a *stronger* statement than the book's (an exact bound, a perfect-
security corollary, a machine-checked reduction with no axioms, or a descent all
the way to field arithmetic), we take that instead of the textbook version —
those cases are called out below. "Have (dev)" means a proof exists in the
development monorepo; the extension is curating clean, self-contained,
book-aligned versions into core, each with its own blueprint chapter. "Blueprint"
points at the foundations the result rests on (already in `blueprint/`); the
example chapters themselves are the roadmap's deliverables.

---

## Landed in core (`CatCryptCore/Examples/`)

Eighteen worked schemes are now formalized directly in core — each core-clean
(imports only core + Mathlib), sorry-free, `lean_verify`-checked to use only the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and carrying its own
blueprint chapter (26 chapters total). The **proof-ladder benchmark is complete**:
symmetric 3/3 (PRF, PRG, Encrypt-then-MAC), asymmetric 1/1 (KEM-DEM), protocol 1/1
(Basic Hash).

| Module | Headline result |
|---|---|
| `OneTimePad` | `otp_perfect_indcpa` — perfect IND-CPA (Adv = 0) |
| `PRG` | `bijPRG_perfect` — perfect PRG security |
| `PRF` | `bijPRF_perfect` — perfect PRF security |
| `CPAFromPRF` | `bijCPA_perfect_indcpa` — a PRF gives IND-CPA encryption |
| `EncryptThenMAC` | `boolEtM_perfect_indcpa` — generic EtM combinator + perfect instantiation |
| `MAC` | `bijMAC_forgery_prob = 1/\|Tag\|` — the information-theoretic optimum |
| `BasicHash` | `auth_zero_advantage_xor` (perfect auth) + unlinkability counterexample |
| `Commitment` | `maskComm_perfect_hiding` + `idComm_perfectly_binding` |
| `SecretSharing` | `ss_perfect_privacy` — 2-of-2 XOR, one share reveals nothing |
| `ShamirSecretSharing` | `shamir_perfect_privacy` — general `t`-of-`n`, any `t−1` shares reveal nothing (+ `shamir_reconstruct`) |
| `KEMDEM` | `pke_security` — full three-term hybrid bound + perfect XOR-DEM |
| `ElGamal` | `elgamal_indcpa_eq_ddh` — exact real-or-random `= DDH` (matches SSProve `OT_CPA`); `elgamal_indcpa_le_ddh` — l-or-r `≤ 2·DDH` |
| `Schnorr` | `schnorr_special_soundness` + `dlFromForking_correct` (forking → DL) |
| `SigmaProtocol` | `simpleSigma_shvzk` + `simpleSigma_special_sound` — SHVZK + special soundness (⇒ `commitment_binding`) |
| `EtMCCA` | `boolEtM_indcca_reduces` — IND-CCA = confidentiality + MAC integrity |
| `CTRMode` | `ctr_perfect_indcpa` — single-block CTR is perfectly IND-CPA |
| `CBCMode` | `cbc_perfect_indcpa` — single-block CBC is perfectly IND-CPA |
| `DiffieHellman` | `ka_advantage_eq_ddh` — DH key indistinguishability = DDH |

`SecurityDefs` now also carries a faithful `INDCCA_Game` (a key-closing decryption
oracle) and the generic `INDCCA_reduces_to_INDCPA`. Perfect CCA is deliberately
*not* claimed — it is impossible in this information-theoretic model — so the CCA
result is the honest authenticated-encryption reduction, not a vacuous Adv = 0.

The fuller / heavier variants and the published-mirror packaging live in the sibling
`catcrypt-examples` layer (requires core only). The block-cipher modes are proved at
the single-block perfect level; multi-block (CTR product-of-bijections, CBC/PRP
chaining) is the honest computational-only frontier, documented per module rather
than faked. With that, the Joy-of-Cryptography curriculum is covered.

---

## Chapter roadmap

| JoC topic | Textbook result | CatCrypt status | Stronger than the book? |
|---|---|---|---|
| One-time pad / perfect secrecy | OTP is perfectly secret | Have (dev: `OTPExample`) | **Yes** — proved as *exact* `Advantage = 0` (information-theoretic), via bijection coupling |
| Pseudorandom generators | PRG security; length extension | Have (dev: `TriplePRG`) | **Yes** — triple-from-double `Adv ≤ 2ε`, *plus* a perfect-security case and a distinguishability *counterexample* |
| PRFs / PRPs / block ciphers | PRF security; PRP/PRF switching | Have (dev: `CascadePRF`, switching lemma) | **Yes** — cascade `Adv ≤ 2ε_prf + q(q-1)/2N` with the birthday term *proved* (not assumed), and a perfect-security corollary |
| CPA security | IND-CPA of PRF-based encryption | Have (dev: `INDCPAExample`) | Matches |
| Block-cipher modes | CTR / CBC security | Have (dev: `CTRMode`, `CBCMode`) | Matches |
| CCA security | IND-CCA; padding attacks | Have (dev: `INDCCA`, `CramerShoup`) | Matches (also a full Cramer–Shoup, beyond the book) |
| MACs | EUF-CMA; CBC-MAC | Have (dev: `CBCMAC`, `EUFCMA`) | Matches |
| Hash functions | collision resistance | Have (dev: `BasicHash`, `Hash`) | **Yes** — perfect authentication *and* an unlinkability counterexample no other treatment gives |
| Authenticated encryption / AEAD | Encrypt-then-MAC; AEAD | Have (dev: `EncryptThenMAC`, `AsconAEAD`) | EtM proved as a combined IND-CCA bound + perfect XOR case |
| Diffie–Hellman / key agreement | DH key exchange | Have (dev: `KeyExchange`) | **Yes** — plus a Curve25519 x-only ladder capstone proved *down to the field arithmetic* (`x25519_ladder_correct_basepoint`) |
| Public-key / ElGamal / hybrid | ElGamal IND-CPA; hybrid encryption | Have (dev: `ThresholdElGamalEx`, `KEMDEM`) | KEM-DEM `Adv ≤ KEM + DEM + KEM` + perfect XOR instantiation |
| Digital signatures | signature security; Schnorr | Have (dev: `Schnorr`, `SchnorrForking`) | Schnorr → DL via the (formalized) general forking lemma |
| Commitments; secret sharing | hiding/binding; threshold sharing | Have (dev: `Commitment`, `SecretSharingEx`) | Matches |

**Suggested first arc into core:** OTP → PRG → PRF → CPA. OTP validates the
examples-in-core + layering pattern end to end; PRG/PRF/CPA are where the
interchangeable-library tactic story first pays off.

---

## Proof-ladder protocols

Concrete evidence that these are real theorems, not slideware: CatCrypt's entries
in the community **[proof-ladders](https://github.com/proof-ladders/) benchmark**,
which pits provers against a fixed challenge set. CatCrypt-Lean is the first Lean 4
entrant and the only one carrying **0 axioms and 0 `sorry`** across its solutions.

| Ladder | Challenges | CatCrypt | Others |
|---|---|:--:|---|
| Symmetric | PRF, PRG, Encrypt-then-MAC | **3/3** | EasyCrypt 3/3, CryptoVerif 1/3 |
| Asymmetric | KEM+DEM PKE | **1/1** | EasyCrypt 1/1, ProofFrog 1/1, Domino 1/1 (draft) |
| Protocol | 6 problems | **1/6** (Basic Hash) | Tamarin 6/6, ProVerif/CryptoVerif/Squirrel 3/6, EasyCrypt 2/6 |
| Implementation | 18 exercises | 0/18 | out of scope (Aeneas/Jasmin territory) |

These `Examples/` (CascadePRF, TriplePRG, EncryptThenMAC, BasicHash, KEMDEM, …) are
exactly the Joy-of-Crypto results above, and are the first candidates to pull into
a core `Examples/` suite.

---

## Comparison with other provers

### Qualitative — do we prove the same theorems?

**On the symmetric ladder and KEM-DEM, yes — and often more.** For PRF, PRG,
Encrypt-then-MAC and KEM-DEM we prove the same computational bound EasyCrypt does,
and additionally a *perfect-security corollary* (`Advantage = 0` for the XOR /
bijection instantiation) that the computational tools don't state. For Basic Hash
we prove perfect authentication and an explicit *negative* result (XOR-hash breaks
unlinkability) that is unique among the ladder solutions.

**Where other tools are genuinely ahead:**
- **EasyCrypt** proves *exact* reductions (equalities, e.g. `Adv_CPA = Adv_CPA(E,R)`), where our combined bounds go through the triangle inequality. That precision is theirs.
- **EasyCrypt** has demonstrated heavy stateful/multi-query reasoning end-to-end (its ~960-line Basic Hash unlinkability proof handles lazy sampling + bad events). We have the tactics and lemmas for this but have not yet driven them through that example.
- **CryptoVerif** is far more concise via built-in crypto macros and automated game-hopping (its Encrypt-then-MAC is ~26 lines) — at the cost of an opaque, tool-internal proof.
- **Tamarin / ProVerif** work in a symbolic model under active attackers with unbounded sessions — a different, stronger threat model than game-based security, and they cover all 6 protocol problems where we cover 1.

**The structural difference:** CatCrypt is a *general-purpose* prover (Lean 4 +
Mathlib); every competitor here is domain-specific (EasyCrypt = crypto pRHL,
CryptoVerif = game-hopping, Tamarin = protocol search). We inherit Mathlib's
mathematics for free (the curve capstone reuses the Weierstrass group law); they
get crypto-specialized automation for free.

### Quantitative — proof size (code lines, one comment-stripped counter, 2026-07-06)

Measured from local sources with a single language-aware counter that drops blank
lines and both block (`(* *)` / `/- -/`) and line (`--`) comments, so "code" means the
same thing for every tool. EasyCrypt = the `proof-ladders` benchmark solutions;
SSProve-Rocq = `coq-ssprove.0.3.0`; CatCrypt = core/dev `Examples/` + shared libs.
Matched on statement strength.

| Challenge (computational) | CatCrypt | SSProve-Rocq | EasyCrypt |
|---|:--:|:--:|:--:|
| PRF cascade | **94** + 214 shared ² | 344 ¹ | 618 + 36 shared |
| PRG triple | **161** | 151 ³ | 255 |
| KEM-DEM (IND-CPA) | 599 | 604 | **200** |
| Basic Hash | 87 ⁴ | — | 191 + 725 ⁴ |
| **Axioms / admitted** | **0** | **0** | 0–13 per file |

¹ SSProve `PRF.v` leaves its birthday `statistical_gap` negligible; CatCrypt's dev
cascade discharges it fully. ² Shared libs (SwitchingLemma 36 + MultiQueryPRF 41 +
BirthdayBound 68 + XorBij 69 = 214 code) amortize across every cascade-style proof.
³ `StretchPRG.v` is the simpler double-from-single variant. ⁴ Not a like-for-like
row: CatCrypt proves perfect auth + an unlinkability *counterexample*; EasyCrypt's 725
lines prove *computational* unlinkability (lazy sampling + bad events).

Read this as *rough magnitude, not a ranking* — the tools count different things and
reflect different proof styles. Two honest takeaways: EasyCrypt's module system wins
KEM-DEM decisively (~3×); on the PRF cascade CatCrypt's proof file is ~6.5× smaller
than EasyCrypt's (94 vs 618), or ~2× once amortized shared libraries are folded in — a
narrower margin than earlier drafts claimed, and with no axioms.

---

## Caveats and attribution

- **This roadmap is flexible.** Prefer the stronger available theorem to the
  textbook one; skip or reorder freely.
- **Layering.** Core examples may use only core foundations, the assumption
  catalog, the tactics, and Mathlib — never a downstream (development-monorepo) import.
  Adapting the dev proofs means extracting the book-level core and stripping
  downstream dependencies.
- **Book-level, not the advanced variant.** Several dev proofs overshoot the book
  (`CramerShoup`, `ThresholdElGamal`, `AsconAEAD`); take the pedagogical core.
- **Attribution.** *The Joy of Cryptography* is CC BY-NC-SA. Definitions and
  theorems are not copyrightable; formalize the *results* with a clear
  "following Rosulek, *The Joy of Cryptography*, §N" credit per module. Do not
  copy the book's prose or figures.
