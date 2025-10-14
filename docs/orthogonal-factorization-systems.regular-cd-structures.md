# Regular cd-structures

<pre class="Agda"><a id="34" class="Keyword">module</a> <a id="41" href="orthogonal-factorization-systems.regular-cd-structures.html" class="Module">orthogonal-factorization-systems.regular-cd-structures</a> <a id="96" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda">
</pre>
</details>

## Idea

A {{#concept "regular cd-structure"}} is a
[cd-structure](orthogonal-factorization-systems.cd-structures.md) which
satisfies the following three axioms:

1. Every distinguished square is [cartesian](foundation.pullbacks.md).
2. The codomain of every distinguished square is an
   [embedding](foundation.embeddings.md).
3. The [diagonal](foundation.diagonals-of-morphisms-arrows.md) of every
   distinguished square
   ```text
         Δ i
      A -----> A ×_X A
      |           |
    f |           | functoriality Δ g
      ∨           ∨
      B -----> B ×_Y B.
         Δ j
   ```
   is again a distinguished square.
