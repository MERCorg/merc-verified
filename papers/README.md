# Papers

Local copies of the literature the formalisation follows (keys as in `references.bib`), for review
against the Lean definitions. The PDFs are not committed (`.gitignore`); this list says where each
one came from, so the folder can be rebuilt.

| key | file | source |
|---|---|---|
| Basten1996 | `Basten1996.pdf` | added by the maintainer (IPL 58(3), doi 10.1016/0020-0190(96)00034-8) |
| Czerwinski2019 | `Czerwinski2019.pdf` | arXiv 1807.10546 |
| DeNicola1995 | `DeNicola1995.pdf` | added by the maintainer (JACM 42(2), doi 10.1145/201019.201032) |
| Erkens2021 (set automaton, ICTAC 2021, with proofs) | `Erkens2021.pdf` | arXiv 2106.15311 |
| Friedmann2009 | `Friedmann2009.pdf` | added by the maintainer (ATVA 2009, doi 10.1007/978-3-642-04761-9_15) |
| Huth2014 | `Huth2014.pdf` | arXiv 1405.0386 |
| Jurdzinski2000 | `Jurdzinski2000.pdf` | author copy, dcs.warwick.ac.uk/~mju |
| Jurdzinski2017 | `Jurdzinski2017.pdf` | arXiv 1702.05051 |
| Keiren2012 (structure graphs, ACM TOCL 13(1)) | `Keiren2012.pdf` | arXiv 1002.3222 |
| Keiren2014 (extended version of the ATVA 2014 paper) | `Keiren2014.pdf` | arXiv 1304.6482v2 |
| Laveaux2021 | `Laveaux2021.pdf` | arXiv 1902.09880 |
| Laveaux2022 (on-the-fly solving, TACAS 2022) | `Laveaux2022.pdf` | arXiv 2201.09607 |
| Laveaux2026 | `Laveaux2026.pdf` | added by the maintainer (doi 10.1007/978-3-032-20684-8_9) |
| Martens2026 | `Martens2026.pdf` | added by the maintainer (doi 10.1007/978-3-032-22752-2_23) |
| Voege2000 | `Voege2000.pdf` | author copy, dcs.warwick.ac.uk/~mju |
| Voorhoeve2001 | `Voorhoeve2001.pdf` | added by the maintainer (IPL 80(1), doi 10.1016/S0020-0190(01)00125-3) |
| Zielonka1998 | `Zielonka1998.pdf` | added by the maintainer (TCS 200(1–2), doi 10.1016/S0304-3975(98)00009-7) |
| vanGlabbeek1996 | `vanGlabbeek1996-PhD.pdf` (thesis; the JACM paper is a chapter) | cgi.cse.unsw.edu.au/~rvg/pub/PhD.pdf |
| (related) van Glabbeek, Luttik, Trčka 2009, *Branching bisimilarity with explicit divergence* | `vanGlabbeek2009-bbed.pdf` | cgi.cse.unsw.edu.au/~rvg/pub/bbed.pdf |
| vandePol2009 | `vandePol2009.pdf` | added by the maintainer (technical report TR-CTIT-09-24) |

## Further parity-game literature (not yet in `references.bib`)

Collected while looking for a Zielonka presentation with strategy computation in the pseudocode.

| file | paper | source | Zielonka pseudocode |
|---|---|---|---|
| `Verver2013.pdf` | M. Verver, *Practical Improvements to Parity Game Solving*, MSc thesis, University of Twente, 2013 | essay.utwente.nl/64985 | **Alg. 5.1 computes the strategy** (a global `strategy` array; attractors assign attractor strategies, the final loop assigns arbitrary successors to the low-priority vertices); §5.1.1 explains it. Basis of mCRL2's `pbespgsolve`. |
| `DiekertKufleitner2022.pdf` | V. Diekert, M. Kufleitner, *Reachability Games and Parity Games* | arXiv 2208.10121 | §6: iterative step list with the strategy construction given in prose next to it, plus a proof that both maximal positional winning strategies are computed |
| `vanDijk2018.pdf`, `vanDijk2018-TACAS.pdf` | T. van Dijk, *Oink: an Implementation and Evaluation of Modern Parity Game Solvers*, TACAS 2018 | arXiv 1801.03859v4; Springer open access, doi 10.1007/978-3-319-89960-2_16 | Alg. 3 (winning regions only; strategies in prose) |
| `vanDijk2024.pdf` | T. van Dijk, *Reproducing parity game algorithms with Oink* | tvandijk.nl/pdf/2024rrrr_oink.pdf | prose only |
| `GazdaWillemse2013.pdf` | M. Gazda, T.A.C. Willemse, *Zielonka's Recursive Algorithm: dull, weak and solitaire games and tighter bounds*, GandALF 2013 | arXiv 1307.4465 | Alg. 1 (winning regions only) |
| `Friedmann2011.pdf` | O. Friedmann, *Recursive algorithm for parity games requires exponential time*, RAIRO-ITA 45(4), 2011 | numdam.org, doi 10.1051/ita/2011124 | Alg. 1 (strategies explicitly omitted) |
| `FriedmannLange-PGSolver.pdf` | O. Friedmann, M. Lange, *The PGSolver Collection of Parity Game Solvers*, v4.1 (manual / tech report) | github.com/tcsprojects/pgsolver, `doc/pgsolver.pdf` | prose only |
| `Sanchez2018.pdf` | L. Sanchez, W. Wesselink, T.A.C. Willemse, *BDD-Based Parity Game Solving: A Comparison of Zielonka's Recursive Algorithm and Priority Promotion*, TU/e CSR-18-01 | win.tue.nl/~timw/downloads/sanchez_paper.pdf | symbolic, winning regions only |
| `DiStasio2021.pdf` | A. Di Stasio, A. Murano, V. Prignano, L. Sorrentino, *Improving parity games in practice*, AMAI 2021 | openaccess.city.ac.uk/id/eprint/33973, doi 10.1007/s10472-020-09721-3 | Alg. 1 (winning regions only) |
