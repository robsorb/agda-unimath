# Principal group actions

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="group-theory.principal-group-actions.html" class="Module">group-theory.principal-group-actions</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="180" class="Keyword">open</a> <a id="185" class="Keyword">import</a> <a id="192" href="foundation.equivalence-extensionality.html" class="Module">foundation.equivalence-extensionality</a>
<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="309" class="Keyword">open</a> <a id="314" class="Keyword">import</a> <a id="321" href="group-theory.groups.html" class="Module">group-theory.groups</a>
</pre>
</details>

## Idea

The **principal group action** is the [action](group-theory.group-actions.md) of
a [group](group-theory.groups.md) on itself by multiplication from the left.

## Definition

<pre class="Agda"><a id="549" class="Keyword">module</a> <a id="556" href="group-theory.principal-group-actions.html#556" class="Module">_</a>
  <a id="560" class="Symbol">{</a><a id="561" href="group-theory.principal-group-actions.html#561" class="Bound">l1</a> <a id="564" class="Symbol">:</a> <a id="566" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="571" class="Symbol">}</a> <a id="573" class="Symbol">(</a><a id="574" href="group-theory.principal-group-actions.html#574" class="Bound">G</a> <a id="576" class="Symbol">:</a> <a id="578" href="group-theory.groups.html#2346" class="Function">Group</a> <a id="584" href="group-theory.principal-group-actions.html#561" class="Bound">l1</a><a id="586" class="Symbol">)</a>
  <a id="590" class="Keyword">where</a>

  <a id="599" href="group-theory.principal-group-actions.html#599" class="Function">principal-action-Group</a> <a id="622" class="Symbol">:</a> <a id="624" href="group-theory.group-actions.html#1098" class="Function">action-Group</a> <a id="637" href="group-theory.principal-group-actions.html#574" class="Bound">G</a> <a id="639" href="group-theory.principal-group-actions.html#561" class="Bound">l1</a>
  <a id="644" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="648" href="group-theory.principal-group-actions.html#599" class="Function">principal-action-Group</a> <a id="671" class="Symbol">=</a> <a id="673" href="group-theory.groups.html#2535" class="Function">set-Group</a> <a id="683" href="group-theory.principal-group-actions.html#574" class="Bound">G</a>
  <a id="687" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="691" class="Symbol">(</a><a id="692" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="696" href="group-theory.principal-group-actions.html#599" class="Function">principal-action-Group</a><a id="718" class="Symbol">)</a> <a id="720" href="group-theory.principal-group-actions.html#720" class="Bound">g</a> <a id="722" class="Symbol">=</a> <a id="724" href="group-theory.groups.html#8607" class="Function">equiv-mul-Group</a> <a id="740" href="group-theory.principal-group-actions.html#574" class="Bound">G</a> <a id="742" href="group-theory.principal-group-actions.html#720" class="Bound">g</a>
  <a id="746" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="750" class="Symbol">(</a><a id="751" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="755" href="group-theory.principal-group-actions.html#599" class="Function">principal-action-Group</a><a id="777" class="Symbol">)</a> <a id="779" class="Symbol">{</a><a id="780" href="group-theory.principal-group-actions.html#780" class="Bound">g</a><a id="781" class="Symbol">}</a> <a id="783" class="Symbol">{</a><a id="784" href="group-theory.principal-group-actions.html#784" class="Bound">h</a><a id="785" class="Symbol">}</a> <a id="787" class="Symbol">=</a>
    <a id="793" href="foundation.equivalence-extensionality.html#2512" class="Function">eq-htpy-equiv</a> <a id="807" class="Symbol">(</a><a id="808" href="group-theory.groups.html#3174" class="Function">associative-mul-Group</a> <a id="830" href="group-theory.principal-group-actions.html#574" class="Bound">G</a> <a id="832" href="group-theory.principal-group-actions.html#780" class="Bound">g</a> <a id="834" href="group-theory.principal-group-actions.html#784" class="Bound">h</a><a id="835" class="Symbol">)</a>
</pre>