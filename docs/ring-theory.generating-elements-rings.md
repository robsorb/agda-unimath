# Generating elements of rings

<pre class="Agda"><a id="41" class="Keyword">module</a> <a id="48" href="ring-theory.generating-elements-rings.html" class="Module">ring-theory.generating-elements-rings</a> <a id="86" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="142" class="Keyword">open</a> <a id="147" class="Keyword">import</a> <a id="154" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="178" class="Keyword">open</a> <a id="183" class="Keyword">import</a> <a id="190" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="218" class="Keyword">open</a> <a id="223" class="Keyword">import</a> <a id="230" href="group-theory.generating-elements-groups.html" class="Module">group-theory.generating-elements-groups</a>

<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
</details>

## Idea

A **generating element** of a [ring](ring-theory.rings.md) `R` is an element `g`
which is a [generating element](group-theory.generating-elements-groups.md) of
the underlying additive [group](group-theory.groups.md) of `R`. That is, `g` is
a generating element of a ring `R` if for every element `x : R` there exists an
integer `k` such that `kg ＝ x`.

## Definitions

### Generating elements of a ring

<pre class="Agda"><a id="739" class="Keyword">module</a> <a id="746" href="ring-theory.generating-elements-rings.html#746" class="Module">_</a>
  <a id="750" class="Symbol">{</a><a id="751" href="ring-theory.generating-elements-rings.html#751" class="Bound">l</a> <a id="753" class="Symbol">:</a> <a id="755" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="760" class="Symbol">}</a> <a id="762" class="Symbol">(</a><a id="763" href="ring-theory.generating-elements-rings.html#763" class="Bound">R</a> <a id="765" class="Symbol">:</a> <a id="767" href="ring-theory.rings.html#1968" class="Function">Ring</a> <a id="772" href="ring-theory.generating-elements-rings.html#751" class="Bound">l</a><a id="773" class="Symbol">)</a> <a id="775" class="Symbol">(</a><a id="776" href="ring-theory.generating-elements-rings.html#776" class="Bound">g</a> <a id="778" class="Symbol">:</a> <a id="780" href="ring-theory.rings.html#2516" class="Function">type-Ring</a> <a id="790" href="ring-theory.generating-elements-rings.html#763" class="Bound">R</a><a id="791" class="Symbol">)</a>
  <a id="795" class="Keyword">where</a>

  <a id="804" href="ring-theory.generating-elements-rings.html#804" class="Function">is-generating-element-prop-Ring</a> <a id="836" class="Symbol">:</a> <a id="838" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="843" href="ring-theory.generating-elements-rings.html#751" class="Bound">l</a>
  <a id="847" href="ring-theory.generating-elements-rings.html#804" class="Function">is-generating-element-prop-Ring</a> <a id="879" class="Symbol">=</a>
    <a id="885" href="group-theory.generating-elements-groups.html#4864" class="Function">is-generating-element-prop-Group</a> <a id="918" class="Symbol">(</a><a id="919" href="ring-theory.rings.html#2118" class="Function">group-Ring</a> <a id="930" href="ring-theory.generating-elements-rings.html#763" class="Bound">R</a><a id="931" class="Symbol">)</a> <a id="933" href="ring-theory.generating-elements-rings.html#776" class="Bound">g</a>
</pre>