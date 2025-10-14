# Discrete binary relations

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="foundation.discrete-binary-relations.html" class="Module">foundation.discrete-binary-relations</a> <a id="82" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="138" class="Keyword">open</a> <a id="143" class="Keyword">import</a> <a id="150" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="213" class="Keyword">open</a> <a id="218" class="Keyword">import</a> <a id="225" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="249" class="Keyword">open</a> <a id="254" class="Keyword">import</a> <a id="261" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

A [binary relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="binary relation" Agda=is-discrete-Relation}}
if it does not relate any elements, i.e., if the type `R x y` is empty for all
`x y : A`. In other words, a binary relation is discrete if and only if it is
the initial binary relation. This definition ensures that the inclusion of
[discrete directed graphs](graph-theory.discrete-directed-graphs.md) is a left
adjoint to the forgetful functor `(V , E) ↦ (V , ∅)`.

The condition of discreteness of binary relations compares to the condition of
[discreteness](foundation.discrete-reflexive-relations.md) of
[reflexive relations](foundation.reflexive-relations.md) in the sense that both
conditions imply initiality. A discrete binary relation is initial because it is
empty, while a discrete reflexive relation is initial because it is
[torsorial](foundation-core.torsorial-type-families.md) and hence it is an
[identity system](foundation.identity-systems.md).

**Note:** It is also possible to impose the torsoriality condition on an
arbitrary binary relation. However, this leads to the concept of
[functional correspondence](foundation.functional-correspondences.md). That is,
a binary relation `R` on `A` such that `R x` is torsorial for every `x : A` is
the graph of a function.

## Definitions

### The predicate on relations of being discrete

<pre class="Agda"><a id="1734" class="Keyword">module</a> <a id="1741" href="foundation.discrete-binary-relations.html#1741" class="Module">_</a>
  <a id="1745" class="Symbol">{</a><a id="1746" href="foundation.discrete-binary-relations.html#1746" class="Bound">l1</a> <a id="1749" href="foundation.discrete-binary-relations.html#1749" class="Bound">l2</a> <a id="1752" class="Symbol">:</a> <a id="1754" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1759" class="Symbol">}</a> <a id="1761" class="Symbol">{</a><a id="1762" href="foundation.discrete-binary-relations.html#1762" class="Bound">A</a> <a id="1764" class="Symbol">:</a> <a id="1766" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1769" href="foundation.discrete-binary-relations.html#1746" class="Bound">l1</a><a id="1771" class="Symbol">}</a> <a id="1773" class="Symbol">(</a><a id="1774" href="foundation.discrete-binary-relations.html#1774" class="Bound">R</a> <a id="1776" class="Symbol">:</a> <a id="1778" href="foundation.binary-relations.html#1220" class="Function">Relation</a> <a id="1787" href="foundation.discrete-binary-relations.html#1749" class="Bound">l2</a> <a id="1790" href="foundation.discrete-binary-relations.html#1762" class="Bound">A</a><a id="1791" class="Symbol">)</a>
  <a id="1795" class="Keyword">where</a>

  <a id="1804" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a> <a id="1830" class="Symbol">:</a> <a id="1832" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1837" class="Symbol">(</a><a id="1838" href="foundation.discrete-binary-relations.html#1746" class="Bound">l1</a> <a id="1841" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1843" href="foundation.discrete-binary-relations.html#1749" class="Bound">l2</a><a id="1845" class="Symbol">)</a>
  <a id="1849" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a> <a id="1875" class="Symbol">=</a>
    <a id="1881" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1888" href="foundation.discrete-binary-relations.html#1762" class="Bound">A</a> <a id="1890" class="Symbol">(λ</a> <a id="1893" href="foundation.discrete-binary-relations.html#1893" class="Bound">x</a> <a id="1895" class="Symbol">→</a> <a id="1897" href="foundation-core.propositions.html#6925" class="Function">Π-Prop</a> <a id="1904" href="foundation.discrete-binary-relations.html#1762" class="Bound">A</a> <a id="1906" class="Symbol">(λ</a> <a id="1909" href="foundation.discrete-binary-relations.html#1909" class="Bound">y</a> <a id="1911" class="Symbol">→</a> <a id="1913" href="foundation.empty-types.html#2734" class="Function">is-empty-Prop</a> <a id="1927" class="Symbol">(</a><a id="1928" href="foundation.discrete-binary-relations.html#1774" class="Bound">R</a> <a id="1930" href="foundation.discrete-binary-relations.html#1893" class="Bound">x</a> <a id="1932" href="foundation.discrete-binary-relations.html#1909" class="Bound">y</a><a id="1933" class="Symbol">)))</a>

  <a id="1940" href="foundation.discrete-binary-relations.html#1940" class="Function">is-discrete-Relation</a> <a id="1961" class="Symbol">:</a> <a id="1963" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1966" class="Symbol">(</a><a id="1967" href="foundation.discrete-binary-relations.html#1746" class="Bound">l1</a> <a id="1970" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1972" href="foundation.discrete-binary-relations.html#1749" class="Bound">l2</a><a id="1974" class="Symbol">)</a>
  <a id="1978" href="foundation.discrete-binary-relations.html#1940" class="Function">is-discrete-Relation</a> <a id="1999" class="Symbol">=</a> <a id="2001" href="foundation-core.propositions.html#1249" class="Function">type-Prop</a> <a id="2011" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a>

  <a id="2040" href="foundation.discrete-binary-relations.html#2040" class="Function">is-prop-is-discrete-Relation</a> <a id="2069" class="Symbol">:</a> <a id="2071" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="2079" href="foundation.discrete-binary-relations.html#1940" class="Function">is-discrete-Relation</a>
  <a id="2102" href="foundation.discrete-binary-relations.html#2040" class="Function">is-prop-is-discrete-Relation</a> <a id="2131" class="Symbol">=</a> <a id="2133" href="foundation-core.propositions.html#1313" class="Function">is-prop-type-Prop</a> <a id="2151" href="foundation.discrete-binary-relations.html#1804" class="Function">is-discrete-prop-Relation</a>
</pre>
## See also

- [Discrete reflexive relations](foundation.discrete-reflexive-relations.md)
- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete-reflexive graphs](graph-theory.discrete-reflexive-graphs.md)
