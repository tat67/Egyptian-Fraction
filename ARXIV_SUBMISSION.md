# Submitting the paper to arXiv

This guide covers the manuscript in [`paper/`](paper/README_PAPER.md). The upload file is [`paper/arxiv/arxiv_source.tar.gz`](paper/arxiv/arxiv_source.tar.gz). Rebuild it with `bash paper/make_arxiv.sh`, which also test-compiles it the way arXiv does: pdfLaTeX only, with the bibliography taken from `main.bbl`.

## 1. Before you submit (the author's own checks)

arXiv holds the listed author responsible for everything in the submission. Since May 2026 it bans authors for one year when a submission shows unchecked AI output: hallucinated references, leftover chatbot comments, or unedited placeholder instructions. See the reports in [Nature](https://www.nature.com/articles/d41586-026-01595-5) and [TechCrunch](https://techcrunch.com/2026/05/16/research-repository-arxiv-will-ban-authors-for-a-year-if-they-let-ai-do-all-the-work/).

The manuscript was drafted with Claude Code, so the author should do the following personally:

* **Read the whole PDF** and make sure you can stand behind every claim. The computational status of each result is stated in Figure 1 and Sections 6–10.
* **Author name.** The paper lists **John Doe**. arXiv expects real names, and the name in the metadata must match the PDF. If "John Doe" is a stand-in, change `\author{...}` in `paper/main.tex` and rebuild.
* **AI disclosure (Section 13).** It now says: *"No independent review of the code by other people has been carried out."* Change this sentence if someone else has reviewed the code, computations or proofs.
* **References.** All 13 entries were checked on 2026-09-30 against publisher, arXiv or library listings found by web search, and each is cited for what it contains. Direct access to arXiv and to publisher sites was blocked in the environment that prepared the paper. It is still worth opening each item yourself, in particular the preprints Watanabe (arXiv:2009.03275), Li (arXiv:2606.15159) and Czenky et al. (arXiv:2507.03727).
* **Optional.**
  * Johnson (1978) is now mentioned only as recorded in Watanabe's abstract. Secondary sources give it as a letter to the editor in *Crux Mathematicorum* 4 (1978), p. 190, and the Crux back issues are online at the Canadian Mathematical Society. If you check that page, you can cite the letter directly again.
  * You can also compare Watanabe's 17 examples with the 17 solutions of type (i) in Appendix A. By Theorem B they must be among the 23.

## 2. Code and data link

The paper points to the tag **`v1.0`**: <https://github.com/tat67/Egyptian-Fraction/tree/v1.0>. This is a fixed snapshot, not the working branch.

* The repository must be **public**.
* On GitHub, you can turn the tag into a Release: *Releases → Draft a new release → choose tag v1.0*.
* **Zenodo DOI (recommended for long-term archiving).**
  1. Sign in at zenodo.org with GitHub.
  2. Under *GitHub*, switch the repository on.
  3. Publish a GitHub Release. Zenodo archives only releases published *after* the switch is on, so publish the release after enabling it.
  4. Zenodo mints a DOI.
  5. Put the DOI in the arXiv *Comments* field. A later arXiv version can also cite it in the paper.

## 3. arXiv account and endorsement

1. Register at <https://arxiv.org/user/register> with your real name and affiliation.
2. First-time submitters to a category usually need an **endorsement**.
   * For mathematics, since 10 December 2025 an institutional e-mail address alone no longer grants automatic endorsement. See the [arXiv blog](https://blog.arxiv.org/arxiv/2025/12/10/updated-endorsement-policy-for-arxiv-mathematics).
   * When you start the submission, arXiv shows an endorsement code. Send it to an established author in **math.NT**, who endorses you at <https://arxiv.org/auth/endorse>.

## 4. The submission form

1. *Start new submission*. Confirm that you are an author, and choose a license. The default "arXiv.org perpetual, non-exclusive license" keeps journal options open; CC BY 4.0 is also common.
2. **Primary category: math.NT** (Number Theory). A cross-list is optional, for example cs.LO for the Lean part.
3. **Upload** `paper/arxiv/arxiv_source.tar.gz` and let arXiv process it. Check the generated PDF carefully:
   * 35 pages;
   * the references present;
   * Figure 1;
   * Appendix B (the verbatim Lean code with Unicode symbols).
4. **Metadata**. Paste the fields below.
5. Preview, then submit. Submissions received before the daily cutoff are announced the next weekday.

| field | value |
|---|---|
| Title | `Integral sums of reciprocals of distinct squarefree semiprimes: forty-seven terms are necessary, and the extremal representations of 1` |
| Authors | `John Doe` |
| Comments | `35 pages, 1 figure. Code, data and Lean 4 formalization: https://github.com/tat67/Egyptian-Fraction/tree/v1.0` |
| MSC class | `11D68 (Primary) 11Y50, 68V20 (Secondary)` |
| Report number, Journal-ref, DOI | leave empty |

Abstract (1658 characters; the limit is 1920):

```
Let $\mathcal{P}=\{pq: p<q \text{ primes}\}$ be the set of squarefree semiprimes. We prove that if $T\subset\mathcal{P}$ is a nonempty finite set such that $\sum_{n\in T}1/n$ is an integer, then $|T|\ge 47$. Since 47-term representations of 1 are known, 47 is the exact minimum; this confirms a conjecture of Watanabe. We also classify the extremal case: there are exactly 23 sets $T\subset\mathcal{P}$ with $|T|=47$ and $\sum_{n\in T}1/n=1$. Seventeen of them involve only primes at most 73, and each of the other six involves exactly one prime larger than 73, namely 269, 311, 421, 433, 503 or 3779. With the same method we also determined all 48-term representations of 1: there are exactly 620 of them. The proofs are computer-assisted. A $p$-adic argument turns integrality into a congruence condition at every vertex of a graph on the primes. A decomposition into a "core" of small primes and a "large-prime part", together with value, parity and star-size lemmas and an explicit divisor equation for a single edge between two large primes, reduces the problem to a finite exhaustive computation, even though arbitrarily large prime factors are allowed. The enumeration of the cores uses a new pruning bound, a Lagrangian relaxation of the value condition combined with a knapsack over residues; the computation uses exact integer arithmetic only. The analytic reduction and the 23 solutions are verified in Lean 4 with Mathlib. The core enumeration is written as a Lean function, and Lean proves that this search is exhaustive; the remaining completion step enters the Lean proofs as explicitly stated hypotheses, which are established by computation.
```

## 5. After the announcement

* Mistakes can be corrected by a *replacement*, which creates version v2. Earlier versions stay visible.
* When the paper is published, add the journal reference and DOI to the arXiv metadata.
