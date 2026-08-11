# Primary-source verification for Version 6.0

Checked on 11 August 2026. This note documents the source interpretation used in the manuscript; it is not an additional mathematical assumption.

## 1. Eric Allender, 2023 prize column

Author draft:
https://people.cs.rutgers.edu/~allender/papers/sigact.news.draft.pdf

Relevant location: Section 4, **“ACC^0 Again: A Retraction”**, pages 4-5 of the PDF.

The section first identifies Hansen's result as the planar constant-width characterization of `ACC^0`. It then describes Allender--Datta--Roy as an extension from genus zero to genus `log^{O(1)} n`, explains that the published proof is incorrect, and immediately states **Open Question 3** with the $1000 reward.

This is the basis for reading Open Question 3 as asking for the unresolved genus extension of the Hansen model, rather than introducing a new unrelated circuit convention.

## 2. Kristoffer Arnsfelt Hansen, ECCC TR03-025

ECCC record:
https://eccc.weizmann.ac.il/report/2003/025/

Relevant location: preliminary paper, page 4, section **“Bounded width branching programs and circuits.”**

Hansen explicitly defines constant-width circuits with:
- fan-in 2 AND gates;
- fan-in 2 OR gates;
- fan-in 1 COPY gates;
- literal or Boolean-constant input nodes;
- a layered constant-width dependency digraph.

This is exactly the source basis stated in Version 6.0 and used by the Lean source-circuit model.

## 3. Allender--Datta--Roy, ECCC TR04-108

ECCC record:
https://eccc.weizmann.ac.il/report/2004/108/

The abstract says that the result extends Hansen's planar characterization to constant-width circuits of **polynomial size and polylogarithmic genus**.

Theorem 6 (page 5 of the PDF) states the same polynomial-size/polylogarithmic-genus characterization and begins its proof by invoking Hansen for the genus-zero direction.

Definition 2 (page 2) gives the layered AND/OR/literal framework but does not separately restate the AND/OR arity. Later, the paper uses one-input “dummy OR” gates, which serve the semantic role of COPY gates. Version 6.0 therefore follows Hansen's explicit arity convention and states that convention rather than silently inferring a higher-fan-in normalization theorem.

## 4. ECCC correction status

The ECCC record for TR04-108 contains Eric Allender's comment accepted 2 November 2025 stating that the proof of Theorem 6 is incorrect and that the truth of the theorem was not known at that time.

Version 6.0 therefore presents a new candidate proof rather than treating the old theorem as established.

## Scope conclusion

The primary-source chain strongly supports the following reading used in Version 6.0:

- source circuits are the Hansen-style constant-width layered circuits;
- the intended disputed extension is from genus zero to polylogarithmic genus;
- the disputed Allender--Datta--Roy theorem is explicitly polynomial-size;
- the one-line prize question does not repeat every convention, so Version 6.0 records the interpretation transparently instead of hiding it.

If Eric Allender were to declare that he intended a strictly broader arbitrary-higher-fan-in or size-free model, that would be a different statement and would require an additional argument. Version 6.0 does not claim such an extension.
