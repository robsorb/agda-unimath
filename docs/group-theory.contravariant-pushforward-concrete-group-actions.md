# Contravariant pushforwards of concrete group actions

<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="group-theory.contravariant-pushforward-concrete-group-actions.html" class="Module">group-theory.contravariant-pushforward-concrete-group-actions</a> <a id="134" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="190" class="Keyword">open</a> <a id="195" class="Keyword">import</a> <a id="202" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="230" class="Keyword">open</a> <a id="235" class="Keyword">import</a> <a id="242" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="group-theory.homomorphisms-concrete-groups.html" class="Module">group-theory.homomorphisms-concrete-groups</a>
</pre>
</details>

## Definition

<pre class="Agda"><a id="366" class="Keyword">module</a> <a id="373" href="group-theory.contravariant-pushforward-concrete-group-actions.html#373" class="Module">_</a>
  <a id="377" class="Symbol">{</a><a id="378" href="group-theory.contravariant-pushforward-concrete-group-actions.html#378" class="Bound">l1</a> <a id="381" href="group-theory.contravariant-pushforward-concrete-group-actions.html#381" class="Bound">l2</a> <a id="384" class="Symbol">:</a> <a id="386" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="391" class="Symbol">}</a> <a id="393" class="Symbol">(</a><a id="394" href="group-theory.contravariant-pushforward-concrete-group-actions.html#394" class="Bound">G</a> <a id="396" class="Symbol">:</a> <a id="398" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="413" href="group-theory.contravariant-pushforward-concrete-group-actions.html#378" class="Bound">l1</a><a id="415" class="Symbol">)</a> <a id="417" class="Symbol">(</a><a id="418" href="group-theory.contravariant-pushforward-concrete-group-actions.html#418" class="Bound">H</a> <a id="420" class="Symbol">:</a> <a id="422" href="group-theory.concrete-groups.html#1102" class="Function">Concrete-Group</a> <a id="437" href="group-theory.contravariant-pushforward-concrete-group-actions.html#381" class="Bound">l2</a><a id="439" class="Symbol">)</a>
  <a id="443" class="Symbol">(</a><a id="444" href="group-theory.contravariant-pushforward-concrete-group-actions.html#444" class="Bound">f</a> <a id="446" class="Symbol">:</a> <a id="448" href="group-theory.homomorphisms-concrete-groups.html#678" class="Function">hom-Concrete-Group</a> <a id="467" href="group-theory.contravariant-pushforward-concrete-group-actions.html#394" class="Bound">G</a> <a id="469" href="group-theory.contravariant-pushforward-concrete-group-actions.html#418" class="Bound">H</a><a id="470" class="Symbol">)</a>
  <a id="474" class="Keyword">where</a>

<a id="481" class="Comment">{-
  contravariant-pushforward-action-Concrete-Group :
    {l : Level} → action-Concrete-Group l G → action-Concrete-Group {!!} H
  contravariant-pushforward-action-Concrete-Group X y = {!!}

    -- The following should be constructed as a set
    hom-action-Concrete-Group G X
      ( subst-action-Concrete-Group G H f (λ y → Id (shape-Concrete-Group H) y))
      -}</a>
</pre>