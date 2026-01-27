# Orbits of concrete group actions

<pre class="Agda"><a id="45" class="Keyword">module</a> <a id="52" href="group-theory.orbits-concrete-group-actions.html" class="Module">group-theory.orbits-concrete-group-actions</a> <a id="95" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="151" class="Keyword">open</a> <a id="156" class="Keyword">import</a> <a id="163" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="195" class="Keyword">open</a> <a id="200" class="Keyword">import</a> <a id="207" href="foundation.function-types.html" class="Module">foundation.function-types</a>
<a id="233" class="Keyword">open</a> <a id="238" class="Keyword">import</a> <a id="245" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="261" class="Keyword">open</a> <a id="266" class="Keyword">import</a> <a id="273" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="301" class="Keyword">open</a> <a id="306" class="Keyword">import</a> <a id="313" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="349" class="Keyword">open</a> <a id="354" class="Keyword">import</a> <a id="361" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
</pre>
</details>

## Idea

The type of **orbits** of a
[concrete group action](group-theory.concrete-group-actions.md) of `G` on `X` is
defined to be the [total space](foundation.dependent-pair-types.md)

```text
  Σ (u : BG), X u.
```

of the type family `X` over the classifying type of the
[concrete group](group-theory.concrete-groups.md) `G`. The idea is that the
"standard" elements of this type are of the form `(* , x)`, where `x` is an
element of the underlying [set](foundation-core.sets.md) `X *` of `X`, and that
the type of [identifications](foundation-core.identity-types.md) from `(* , x)`
to `(* , y)` is [equivalent](foundation-core.equivalences.md) to the type

```text
  Σ (g : G), g x ＝ y.
```

In other words, identifications between the elements `(* , x)` and `(* , y)` in
the type of orbits of `X` are equivalently described as group elements `g` such
that `g x ＝ y`.

Note that the type of orbits of a concrete group is typically a
[`1`-type](foundation-core.1-types.md). In
[Free concrete group actions](group-theory.free-concrete-group-actions.md) we
will show that the type of orbits is a set if and only if the action of `G` on
`X` is free, and in
[Transitive concrete group actions](group-theory.transitive-concrete-group-actions.md)
we will show that the type of orbits is
[`0`-connected](foundation.0-connected-types.md) if and only if the action is
transitive.

## Definition

<pre class="Agda"><a id="orbit-action-Concrete-Group"></a><a id="1806" href="group-theory.orbits-concrete-group-actions.html#1806" class="Function">orbit-action-Concrete-Group</a> <a id="1834" class="Symbol">:</a>
  <a id="1838" class="Symbol">{</a><a id="1839" href="group-theory.orbits-concrete-group-actions.html#1839" class="Bound">l1</a> <a id="1842" href="group-theory.orbits-concrete-group-actions.html#1842" class="Bound">l2</a> <a id="1845" class="Symbol">:</a> <a id="1847" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1852" class="Symbol">}</a> <a id="1854" class="Symbol">(</a><a id="1855" href="group-theory.orbits-concrete-group-actions.html#1855" class="Bound">G</a> <a id="1857" class="Symbol">:</a> <a id="1859" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="1874" href="group-theory.orbits-concrete-group-actions.html#1839" class="Bound">l1</a><a id="1876" class="Symbol">)</a> <a id="1878" class="Symbol">(</a><a id="1879" href="group-theory.orbits-concrete-group-actions.html#1879" class="Bound">X</a> <a id="1881" class="Symbol">:</a> <a id="1883" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="1905" href="group-theory.orbits-concrete-group-actions.html#1842" class="Bound">l2</a> <a id="1908" href="group-theory.orbits-concrete-group-actions.html#1855" class="Bound">G</a><a id="1909" class="Symbol">)</a> <a id="1911" class="Symbol">→</a>
  <a id="1915" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1918" class="Symbol">(</a><a id="1919" href="group-theory.orbits-concrete-group-actions.html#1839" class="Bound">l1</a> <a id="1922" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1924" href="group-theory.orbits-concrete-group-actions.html#1842" class="Bound">l2</a><a id="1926" class="Symbol">)</a>
<a id="1928" href="group-theory.orbits-concrete-group-actions.html#1806" class="Function">orbit-action-Concrete-Group</a> <a id="1956" href="group-theory.orbits-concrete-group-actions.html#1956" class="Bound">G</a> <a id="1958" href="group-theory.orbits-concrete-group-actions.html#1958" class="Bound">X</a> <a id="1960" class="Symbol">=</a>
  <a id="1964" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1966" class="Symbol">(</a><a id="1967" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="1999" href="group-theory.orbits-concrete-group-actions.html#1956" class="Bound">G</a><a id="2000" class="Symbol">)</a> <a id="2002" class="Symbol">(</a><a id="2003" href="foundation-core.sets.html#1025" class="Function">type-Set</a> <a id="2012" href="foundation-core.function-types.html#504" class="Function Operator">∘</a> <a id="2014" href="group-theory.orbits-concrete-group-actions.html#1958" class="Bound">X</a><a id="2015" class="Symbol">)</a>
</pre>
## See also

- [Free concrete group actions](group-theory.free-concrete-group-actions.md)
- [Transitive concrete group actions](group-theory.transitive-concrete-group-actions.md)
