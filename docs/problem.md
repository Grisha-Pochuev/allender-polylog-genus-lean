# The problem

## Allender's Open Question 3

Eric Allender asked whether every language accepted by constant-width circuit families of polylogarithmic genus lies in `ACC⁰`. The question appears in Section 4 of his 2023 SIGACT News column and carries a US $1000 bounty.

The intended source model is a family of Boolean circuits `{Cₙ}` with:

- width bounded by one constant independent of `n`;
- polynomial size;
- underlying circuit graph embeddable in an orientable surface of genus `(log n)^{O(1)}`.

The required conclusion is that the recognized language belongs to `ACC⁰`, the class of polynomial-size, constant-depth Boolean circuits with unbounded-fan-in `AND`, `OR`, `NOT`, and modular counting gates for fixed moduli.

## Historical context

Hansen proved that polynomial-size planar constant-width circuits characterize `ACC⁰`. Allender, Datta, and Roy later claimed that allowing polylogarithmic genus gives no additional power. Allender subsequently identified an error in the proof of the main theorem of that work and stated that the theorem is not known.

The invalid step concerned a claimed linear arrangement of handle connections on a cylinder. This repository must not use that arrangement, explicitly or implicitly.

## Primary references

1. Eric Allender, *Parting Thoughts and Parting Shots (Read On for Details on How to Win Valuable Prizes!)*, SIGACT News 54(1), 2023, pp. 63–81.  
   https://people.cs.rutgers.edu/~allender/papers/sigact.news.draft.pdf
2. Eric Allender, Samir Datta, Sambuddha Roy, *Topology inside NC¹*, CCC 2005; ECCC TR04-108.  
   https://eccc.weizmann.ac.il/eccc-reports/2004/TR04-108/index.html
3. Kristoffer Arnsfelt Hansen, *Constant Width Planar Computation Characterizes ACC⁰*, Theory of Computing Systems 39(1), 2006, pp. 79–92.

## Bounty fine print relevant to publication

Allender's article says that the rewards are for solutions first made public after March 2023, are denominated in US dollars, and remain subject to his ability to verify the claim. The article does not require publication in a named journal or repository.

## Formal target

A future final theorem should quantify over a precise Boolean-circuit model and prove an implication of the form:

```text
constant width
+ polynomial size
+ polylogarithmic orientable genus
----------------------------------
              ACC⁰
```

No theorem currently in this repository asserts this implication.
