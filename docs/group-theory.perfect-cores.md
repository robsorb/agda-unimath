# Perfect cores

<pre class="Agda"><a id="26" class="Keyword">module</a> <a id="33" href="group-theory.perfect-cores.html" class="Module">group-theory.perfect-cores</a> <a id="60" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="116" class="Keyword">open</a> <a id="121" class="Keyword">import</a> <a id="128" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="160" class="Keyword">open</a> <a id="165" class="Keyword">import</a> <a id="172" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="200" class="Keyword">open</a> <a id="205" class="Keyword">import</a> <a id="212" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="group-theory.perfect-subgroups.html" class="Module">group-theory.perfect-subgroups</a>
<a id="275" class="Keyword">open</a> <a id="280" class="Keyword">import</a> <a id="287" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
</pre>
</details>

## Idea

The **perfect core** of a [group](group-theory.groups.md) `G` is the largest
[perfect subgroup](group-theory.perfect-subgroups.md) of `G`. That is, the
[subgroup](group-theory.subgroups.md) `perfect-core G` satisfies the following
universal property:

```text
  (H : Subgroup G) → is-perfect-Subgroup G H ↔ H ⊆ perfect-core G
```

## Definitions

### The predicate of being a perfect core

<pre class="Agda"><a id="734" class="Keyword">module</a> <a id="741" href="group-theory.perfect-cores.html#741" class="Module">_</a>
  <a id="745" class="Symbol">{</a><a id="746" href="group-theory.perfect-cores.html#746" class="Bound">l1</a> <a id="749" href="group-theory.perfect-cores.html#749" class="Bound">l2</a> <a id="752" class="Symbol">:</a> <a id="754" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="759" class="Symbol">}</a> <a id="761" class="Symbol">(</a><a id="762" href="group-theory.perfect-cores.html#762" class="Bound">G</a> <a id="764" class="Symbol">:</a> <a id="766" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="772" href="group-theory.perfect-cores.html#746" class="Bound">l1</a><a id="774" class="Symbol">)</a> <a id="776" class="Symbol">(</a><a id="777" href="group-theory.perfect-cores.html#777" class="Bound">H</a> <a id="779" class="Symbol">:</a> <a id="781" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="790" href="group-theory.perfect-cores.html#749" class="Bound">l2</a> <a id="793" href="group-theory.perfect-cores.html#762" class="Bound">G</a><a id="794" class="Symbol">)</a>
  <a id="798" class="Keyword">where</a>

  <a id="807" href="group-theory.perfect-cores.html#807" class="Function">is-perfect-core-Subgroup</a> <a id="832" class="Symbol">:</a> <a id="834" href="Agda.Primitive.html#512" class="Primitive">UUω</a>
  <a id="840" href="group-theory.perfect-cores.html#807" class="Function">is-perfect-core-Subgroup</a> <a id="865" class="Symbol">=</a>
    <a id="871" class="Symbol">{</a><a id="872" href="group-theory.perfect-cores.html#872" class="Bound">l</a> <a id="874" class="Symbol">:</a> <a id="876" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="881" class="Symbol">}</a> <a id="883" class="Symbol">(</a><a id="884" href="group-theory.perfect-cores.html#884" class="Bound">K</a> <a id="886" class="Symbol">:</a> <a id="888" href="group-theory.subgroups.html#3914" class="Function">Subgroup</a> <a id="897" href="group-theory.perfect-cores.html#872" class="Bound">l</a> <a id="899" href="group-theory.perfect-cores.html#762" class="Bound">G</a><a id="900" class="Symbol">)</a> <a id="902" class="Symbol">→</a>
    <a id="908" href="group-theory.perfect-subgroups.html#777" class="Function">is-perfect-Subgroup</a> <a id="928" href="group-theory.perfect-cores.html#762" class="Bound">G</a> <a id="930" href="group-theory.perfect-cores.html#884" class="Bound">K</a> <a id="932" href="foundation.logical-equivalences.html#2096" class="Function Operator">↔</a> <a id="934" href="group-theory.subgroups.html#13941" class="Function">leq-Subgroup</a> <a id="947" href="group-theory.perfect-cores.html#762" class="Bound">G</a> <a id="949" href="group-theory.perfect-cores.html#884" class="Bound">K</a> <a id="951" href="group-theory.perfect-cores.html#777" class="Bound">H</a>
</pre>
## External links

- [Perfect core](https://en.wikipedia.org/wiki/Perfect_core) at Wikipedia

A wikidata identifier was not available for this concept.
