# Diagonal span diagrams

<pre class="Agda"><a id="35" class="Keyword">module</a> <a id="42" href="foundation.diagonal-span-diagrams.html" class="Module">foundation.diagonal-span-diagrams</a> <a id="76" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="132" class="Keyword">open</a> <a id="137" class="Keyword">import</a> <a id="144" href="foundation.span-diagrams.html" class="Module">foundation.span-diagrams</a>
<a id="169" class="Keyword">open</a> <a id="174" class="Keyword">import</a> <a id="181" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Consider a map `f : A → B`. The
{{#concept "diagonal span diagram" Agda=diagonal-span-diagram}} of `f` is the
[span diagram](foundation.span-diagrams.md)

```text
       f       f
  B <----- A -----> B.
```

## Definitions

### Diagonal span diagrams of maps

<pre class="Agda"><a id="502" class="Keyword">module</a> <a id="509" href="foundation.diagonal-span-diagrams.html#509" class="Module">_</a>
  <a id="513" class="Symbol">{</a><a id="514" href="foundation.diagonal-span-diagrams.html#514" class="Bound">l1</a> <a id="517" href="foundation.diagonal-span-diagrams.html#517" class="Bound">l2</a> <a id="520" class="Symbol">:</a> <a id="522" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="527" class="Symbol">}</a> <a id="529" class="Symbol">{</a><a id="530" href="foundation.diagonal-span-diagrams.html#530" class="Bound">A</a> <a id="532" class="Symbol">:</a> <a id="534" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="537" href="foundation.diagonal-span-diagrams.html#514" class="Bound">l1</a><a id="539" class="Symbol">}</a> <a id="541" class="Symbol">{</a><a id="542" href="foundation.diagonal-span-diagrams.html#542" class="Bound">B</a> <a id="544" class="Symbol">:</a> <a id="546" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="549" href="foundation.diagonal-span-diagrams.html#517" class="Bound">l2</a><a id="551" class="Symbol">}</a> <a id="553" class="Symbol">(</a><a id="554" href="foundation.diagonal-span-diagrams.html#554" class="Bound">f</a> <a id="556" class="Symbol">:</a> <a id="558" href="foundation.diagonal-span-diagrams.html#530" class="Bound">A</a> <a id="560" class="Symbol">→</a> <a id="562" href="foundation.diagonal-span-diagrams.html#542" class="Bound">B</a><a id="563" class="Symbol">)</a>
  <a id="567" class="Keyword">where</a>

  <a id="576" href="foundation.diagonal-span-diagrams.html#576" class="Function">diagonal-span-diagram</a> <a id="598" class="Symbol">:</a> <a id="600" href="foundation.span-diagrams.html#1505" class="Function">span-diagram</a> <a id="613" href="foundation.diagonal-span-diagrams.html#517" class="Bound">l2</a> <a id="616" href="foundation.diagonal-span-diagrams.html#517" class="Bound">l2</a> <a id="619" href="foundation.diagonal-span-diagrams.html#514" class="Bound">l1</a>
  <a id="624" href="foundation.diagonal-span-diagrams.html#576" class="Function">diagonal-span-diagram</a> <a id="646" class="Symbol">=</a> <a id="648" href="foundation.span-diagrams.html#1726" class="Function">make-span-diagram</a> <a id="666" href="foundation.diagonal-span-diagrams.html#554" class="Bound">f</a> <a id="668" href="foundation.diagonal-span-diagrams.html#554" class="Bound">f</a>
</pre>