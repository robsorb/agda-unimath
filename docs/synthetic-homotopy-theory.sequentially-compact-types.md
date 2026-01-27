# Sequentially compact types

<pre class="Agda"><a id="39" class="Keyword">module</a> <a id="46" href="synthetic-homotopy-theory.sequentially-compact-types.html" class="Module">synthetic-homotopy-theory.sequentially-compact-types</a> <a id="99" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="155" class="Keyword">open</a> <a id="160" class="Keyword">import</a> <a id="167" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="191" class="Keyword">open</a> <a id="196" class="Keyword">import</a> <a id="203" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="231" class="Keyword">open</a> <a id="236" class="Keyword">import</a> <a id="243" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html" class="Module">synthetic-homotopy-theory.cocones-under-sequential-diagrams</a>
<a id="303" class="Keyword">open</a> <a id="308" class="Keyword">import</a> <a id="315" href="synthetic-homotopy-theory.sequential-diagrams.html" class="Module">synthetic-homotopy-theory.sequential-diagrams</a>
<a id="361" class="Keyword">open</a> <a id="366" class="Keyword">import</a> <a id="373" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html" class="Module">synthetic-homotopy-theory.universal-property-sequential-colimits</a>
</pre>
</details>

## Idea

A **sequentially compact type** is a type `X` such that exponentiating by `X`
commutes with
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)

```text
  colimₙ (X → Aₙ) ≃ (X → colimₙ Aₙ)
```

for every [cotower](synthetic-homotopy-theory.sequential-diagrams.md) `Aₙ`.

## Definitions

### The predicate of being a sequentially compact type

<pre class="Agda"><a id="854" class="Keyword">module</a> <a id="861" href="synthetic-homotopy-theory.sequentially-compact-types.html#861" class="Module">_</a>
  <a id="865" class="Symbol">{</a><a id="866" href="synthetic-homotopy-theory.sequentially-compact-types.html#866" class="Bound">l1</a> <a id="869" class="Symbol">:</a> <a id="871" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="876" class="Symbol">}</a> <a id="878" class="Symbol">(</a><a id="879" href="synthetic-homotopy-theory.sequentially-compact-types.html#879" class="Bound">X</a> <a id="881" class="Symbol">:</a> <a id="883" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="886" href="synthetic-homotopy-theory.sequentially-compact-types.html#866" class="Bound">l1</a><a id="888" class="Symbol">)</a>
  <a id="892" class="Keyword">where</a>

  <a id="901" href="synthetic-homotopy-theory.sequentially-compact-types.html#901" class="Function">is-sequentially-compact</a> <a id="925" class="Symbol">:</a> <a id="927" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="933" href="synthetic-homotopy-theory.sequentially-compact-types.html#901" class="Function">is-sequentially-compact</a> <a id="957" class="Symbol">=</a>
    <a id="963" class="Symbol">{</a><a id="964" href="synthetic-homotopy-theory.sequentially-compact-types.html#964" class="Bound">l2</a> <a id="967" href="synthetic-homotopy-theory.sequentially-compact-types.html#967" class="Bound">l3</a> <a id="970" class="Symbol">:</a> <a id="972" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="977" class="Symbol">}</a> <a id="979" class="Symbol">(</a><a id="980" href="synthetic-homotopy-theory.sequentially-compact-types.html#980" class="Bound">A</a> <a id="982" class="Symbol">:</a> <a id="984" href="synthetic-homotopy-theory.sequential-diagrams.html#872" class="Function">sequential-diagram</a> <a id="1003" href="synthetic-homotopy-theory.sequentially-compact-types.html#964" class="Bound">l2</a><a id="1005" class="Symbol">)</a> <a id="1007" class="Symbol">{</a><a id="1008" href="synthetic-homotopy-theory.sequentially-compact-types.html#1008" class="Bound">A∞</a> <a id="1011" class="Symbol">:</a> <a id="1013" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1016" href="synthetic-homotopy-theory.sequentially-compact-types.html#967" class="Bound">l3</a><a id="1018" class="Symbol">}</a>
    <a id="1024" class="Symbol">(</a><a id="1025" href="synthetic-homotopy-theory.sequentially-compact-types.html#1025" class="Bound">c</a> <a id="1027" class="Symbol">:</a> <a id="1029" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#1775" class="Function">cocone-sequential-diagram</a> <a id="1055" href="synthetic-homotopy-theory.sequentially-compact-types.html#980" class="Bound">A</a> <a id="1057" href="synthetic-homotopy-theory.sequentially-compact-types.html#1008" class="Bound">A∞</a><a id="1059" class="Symbol">)</a> <a id="1061" class="Symbol">→</a>
    <a id="1067" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a> <a id="1105" href="synthetic-homotopy-theory.sequentially-compact-types.html#1025" class="Bound">c</a> <a id="1107" class="Symbol">→</a>
    <a id="1113" href="synthetic-homotopy-theory.universal-property-sequential-colimits.html#2517" class="Function">universal-property-sequential-colimit</a>
      <a id="1157" class="Symbol">(</a> <a id="1159" href="synthetic-homotopy-theory.cocones-under-sequential-diagrams.html#7675" class="Function">cocone-postcomp-sequential-diagram</a> <a id="1194" href="synthetic-homotopy-theory.sequentially-compact-types.html#879" class="Bound">X</a> <a id="1196" href="synthetic-homotopy-theory.sequentially-compact-types.html#980" class="Bound">A</a> <a id="1198" href="synthetic-homotopy-theory.sequentially-compact-types.html#1025" class="Bound">c</a><a id="1199" class="Symbol">)</a>
</pre>
## References

{{#bibliography}} {{#reference Rij19}}
