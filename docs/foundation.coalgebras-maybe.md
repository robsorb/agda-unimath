# Coalgebras of the maybe monad

<pre class="Agda"><a id="42" class="Keyword">module</a> <a id="49" href="foundation.coalgebras-maybe.html" class="Module">foundation.coalgebras-maybe</a> <a id="77" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="133" class="Keyword">open</a> <a id="138" class="Keyword">import</a> <a id="145" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="177" class="Keyword">open</a> <a id="182" class="Keyword">import</a> <a id="189" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="206" class="Keyword">open</a> <a id="211" class="Keyword">import</a> <a id="218" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="trees.polynomial-endofunctors.html" class="Module">trees.polynomial-endofunctors</a>
</pre>
</details>

## Idea

A
{{#concept "coalgebra" Disambiguation="of the maybe monad" Agda=coalgebra-Maybe}}
is a type `X` [equipped](foundation.structure.md) with a map

```text
  X → Maybe X.
```

## Definitions

### Maybe-coalgebra structure on a type

<pre class="Agda"><a id="coalgebra-structure-Maybe"></a><a id="553" href="foundation.coalgebras-maybe.html#553" class="Function">coalgebra-structure-Maybe</a> <a id="579" class="Symbol">:</a> <a id="581" class="Symbol">{</a><a id="582" href="foundation.coalgebras-maybe.html#582" class="Bound">l</a> <a id="584" class="Symbol">:</a> <a id="586" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="591" class="Symbol">}</a> <a id="593" class="Symbol">→</a> <a id="595" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="598" href="foundation.coalgebras-maybe.html#582" class="Bound">l</a> <a id="600" class="Symbol">→</a> <a id="602" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="605" href="foundation.coalgebras-maybe.html#582" class="Bound">l</a>
<a id="607" href="foundation.coalgebras-maybe.html#553" class="Function">coalgebra-structure-Maybe</a> <a id="633" href="foundation.coalgebras-maybe.html#633" class="Bound">X</a> <a id="635" class="Symbol">=</a> <a id="637" href="foundation.coalgebras-maybe.html#633" class="Bound">X</a> <a id="639" class="Symbol">→</a> <a id="641" href="foundation.maybe.html#1591" class="Function">Maybe</a> <a id="647" href="foundation.coalgebras-maybe.html#633" class="Bound">X</a>
</pre>
### Maybe-coalgebras

<pre class="Agda"><a id="coalgebra-Maybe"></a><a id="684" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="700" class="Symbol">:</a> <a id="702" class="Symbol">(</a><a id="703" href="foundation.coalgebras-maybe.html#703" class="Bound">l</a> <a id="705" class="Symbol">:</a> <a id="707" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="712" class="Symbol">)</a> <a id="714" class="Symbol">→</a> <a id="716" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="719" class="Symbol">(</a><a id="720" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="725" href="foundation.coalgebras-maybe.html#703" class="Bound">l</a><a id="726" class="Symbol">)</a>
<a id="728" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="744" href="foundation.coalgebras-maybe.html#744" class="Bound">l</a> <a id="746" class="Symbol">=</a> <a id="748" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="750" class="Symbol">(</a><a id="751" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="754" href="foundation.coalgebras-maybe.html#744" class="Bound">l</a><a id="755" class="Symbol">)</a> <a id="757" class="Symbol">(</a><a id="758" href="foundation.coalgebras-maybe.html#553" class="Function">coalgebra-structure-Maybe</a><a id="783" class="Symbol">)</a>

<a id="786" class="Keyword">module</a> <a id="793" href="foundation.coalgebras-maybe.html#793" class="Module">_</a>
  <a id="797" class="Symbol">{</a><a id="798" href="foundation.coalgebras-maybe.html#798" class="Bound">l</a> <a id="800" class="Symbol">:</a> <a id="802" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="807" class="Symbol">}</a> <a id="809" class="Symbol">(</a><a id="810" href="foundation.coalgebras-maybe.html#810" class="Bound">X</a> <a id="812" class="Symbol">:</a> <a id="814" href="foundation.coalgebras-maybe.html#684" class="Function">coalgebra-Maybe</a> <a id="830" href="foundation.coalgebras-maybe.html#798" class="Bound">l</a><a id="831" class="Symbol">)</a>
  <a id="835" class="Keyword">where</a>

  <a id="844" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="865" class="Symbol">:</a> <a id="867" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="870" href="foundation.coalgebras-maybe.html#798" class="Bound">l</a>
  <a id="874" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="895" class="Symbol">=</a> <a id="897" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="901" href="foundation.coalgebras-maybe.html#810" class="Bound">X</a>

  <a id="906" href="foundation.coalgebras-maybe.html#906" class="Function">map-coalgebra-Maybe</a> <a id="926" class="Symbol">:</a> <a id="928" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a> <a id="949" class="Symbol">→</a> <a id="951" href="foundation.maybe.html#1591" class="Function">Maybe</a> <a id="957" href="foundation.coalgebras-maybe.html#844" class="Function">type-coalgebra-Maybe</a>
  <a id="980" href="foundation.coalgebras-maybe.html#906" class="Function">map-coalgebra-Maybe</a> <a id="1000" class="Symbol">=</a> <a id="1002" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1006" href="foundation.coalgebras-maybe.html#810" class="Bound">X</a>
</pre>