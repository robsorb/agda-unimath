# Principal torsors of concrete groups

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="group-theory.principal-torsors-concrete-groups.html" class="Module">group-theory.principal-torsors-concrete-groups</a> <a id="103" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="159" class="Keyword">open</a> <a id="164" class="Keyword">import</a> <a id="171" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="199" class="Keyword">open</a> <a id="204" class="Keyword">import</a> <a id="211" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
</pre>
</details>

## Idea

The **principal torsor** of a [concrete group](group-theory.concrete-groups.md)
`G` is the [identity type](foundation-core.identity-types.md) of `BG`.

## Definition

<pre class="Agda"><a id="489" class="Keyword">module</a> <a id="496" href="group-theory.principal-torsors-concrete-groups.html#496" class="Module">_</a>
  <a id="500" class="Symbol">{</a><a id="501" href="group-theory.principal-torsors-concrete-groups.html#501" class="Bound">l1</a> <a id="504" class="Symbol">:</a> <a id="506" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="511" class="Symbol">}</a> <a id="513" class="Symbol">(</a><a id="514" href="group-theory.principal-torsors-concrete-groups.html#514" class="Bound">G</a> <a id="516" class="Symbol">:</a> <a id="518" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="533" href="group-theory.principal-torsors-concrete-groups.html#501" class="Bound">l1</a><a id="535" class="Symbol">)</a>
  <a id="539" class="Keyword">where</a>

  <a id="548" href="group-theory.principal-torsors-concrete-groups.html#548" class="Function">principal-torsor-Concrete-Group</a> <a id="580" class="Symbol">:</a>
    <a id="586" href="group-theory.concrete-groups.html#1503" class="Function">classifying-type-Concrete-Group</a> <a id="618" href="group-theory.principal-torsors-concrete-groups.html#514" class="Bound">G</a> <a id="620" class="Symbol">→</a> <a id="622" href="group-theory.concrete-group-actions.html#734" class="Function">action-Concrete-Group</a> <a id="644" href="group-theory.principal-torsors-concrete-groups.html#501" class="Bound">l1</a> <a id="647" href="group-theory.principal-torsors-concrete-groups.html#514" class="Bound">G</a>
  <a id="651" href="group-theory.principal-torsors-concrete-groups.html#548" class="Function">principal-torsor-Concrete-Group</a> <a id="683" class="Symbol">=</a> <a id="685" href="group-theory.concrete-groups.html#3642" class="Function">Id-BG-Set</a> <a id="695" href="group-theory.principal-torsors-concrete-groups.html#514" class="Bound">G</a>
</pre>