# Erasing equality

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="reflection.erasing-equality.html" class="Module">reflection.erasing-equality</a> <a id="64" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="120" class="Keyword">open</a> <a id="125" class="Keyword">import</a> <a id="132" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Agda's builtin primitive `primEraseEquality` is a special construct on
[identifications](foundation-core.identity-types.md) that for every
identification `x ＝ y` gives an identification `x ＝ y` with the following
reduction behavior:

- If the two end points `x ＝ y` normalize to the same term, `primEraseEquality`
  reduces to `refl`.

For example, `primEraseEquality` applied to the loop of the
[circle](synthetic-homotopy-theory.circle.md) will compute to `refl`, while
`primEraseEquality` applied to the nontrivial identification in the
[interval](synthetic-homotopy-theory.interval-type.md) will not reduce.

This primitive is useful for [rewrite rules](reflection.rewriting.md), as it
ensures that the identification used in defining the rewrite rule also computes
to `refl`. Concretely, if the identification `β` defines a rewrite rule, and `β`
is defined via `primEraseEqaulity`, then we have the strict equality `β ≐ refl`.

## Primitives

<pre class="Agda"><a id="1185" class="Keyword">primitive</a>
  <a id="primEraseEquality"></a><a id="1197" href="reflection.erasing-equality.html#1197" class="Primitive">primEraseEquality</a> <a id="1215" class="Symbol">:</a> <a id="1217" class="Symbol">{</a><a id="1218" href="reflection.erasing-equality.html#1218" class="Bound">l</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1227" class="Symbol">}</a> <a id="1229" class="Symbol">{</a><a id="1230" href="reflection.erasing-equality.html#1230" class="Bound">A</a> <a id="1232" class="Symbol">:</a> <a id="1234" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1237" href="reflection.erasing-equality.html#1218" class="Bound">l</a><a id="1238" class="Symbol">}</a> <a id="1240" class="Symbol">{</a><a id="1241" href="reflection.erasing-equality.html#1241" class="Bound">x</a> <a id="1243" href="reflection.erasing-equality.html#1243" class="Bound">y</a> <a id="1245" class="Symbol">:</a> <a id="1247" href="reflection.erasing-equality.html#1230" class="Bound">A</a><a id="1248" class="Symbol">}</a> <a id="1250" class="Symbol">→</a> <a id="1252" href="reflection.erasing-equality.html#1241" class="Bound">x</a> <a id="1254" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1256" href="reflection.erasing-equality.html#1243" class="Bound">y</a> <a id="1258" class="Symbol">→</a> <a id="1260" href="reflection.erasing-equality.html#1241" class="Bound">x</a> <a id="1262" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1264" href="reflection.erasing-equality.html#1243" class="Bound">y</a>
</pre>
## External links

- [Built-ins#Equality](https://agda.readthedocs.io/en/latest/language/built-ins.html#equality)
  at Agda's documentation pages
