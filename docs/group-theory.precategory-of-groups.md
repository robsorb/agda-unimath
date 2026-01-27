# The precategory of groups

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a> <a id="80" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="136" class="Keyword">open</a> <a id="141" class="Keyword">import</a> <a id="148" href="category-theory.full-large-subprecategories.html" class="Module">category-theory.full-large-subprecategories</a>
<a id="192" class="Keyword">open</a> <a id="197" class="Keyword">import</a> <a id="204" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="240" class="Keyword">open</a> <a id="245" class="Keyword">import</a> <a id="252" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="283" class="Keyword">open</a> <a id="288" class="Keyword">import</a> <a id="295" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="355" class="Keyword">open</a> <a id="360" class="Keyword">import</a> <a id="367" href="group-theory.precategory-of-semigroups.html" class="Module">group-theory.precategory-of-semigroups</a>
</pre>
</details>

## Definition

### The precategory of groups as a full subprecategory of the precategory of semigroups

<pre class="Agda"><a id="Group-Full-Large-Subprecategory"></a><a id="535" href="group-theory.precategory-of-groups.html#535" class="Function">Group-Full-Large-Subprecategory</a> <a id="567" class="Symbol">:</a>
  <a id="571" href="category-theory.full-large-subprecategories.html#1584" class="Function">Full-Large-Subprecategory</a> <a id="597" class="Symbol">(λ</a> <a id="600" href="group-theory.precategory-of-groups.html#600" class="Bound">l</a> <a id="602" class="Symbol">→</a> <a id="604" href="group-theory.precategory-of-groups.html#600" class="Bound">l</a><a id="605" class="Symbol">)</a> <a id="607" href="group-theory.precategory-of-semigroups.html#469" class="Function">Semigroup-Large-Precategory</a>
<a id="635" href="group-theory.precategory-of-groups.html#535" class="Function">Group-Full-Large-Subprecategory</a> <a id="667" class="Symbol">=</a> <a id="669" href="group-theory.groups.html#20173" class="Function">is-group-prop-Semigroup</a>
</pre>
### The large precategory of groups

<pre class="Agda"><a id="Group-Large-Precategory"></a><a id="743" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="767" class="Symbol">:</a> <a id="769" href="category-theory.large-precategories.html#829" class="Record">Large-Precategory</a> <a id="787" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="792" class="Symbol">(</a><a id="793" href="Agda.Primitive.html#961" class="Primitive Operator">_⊔_</a><a id="796" class="Symbol">)</a>
<a id="798" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a> <a id="822" class="Symbol">=</a>
  <a id="826" href="category-theory.full-large-subprecategories.html#5854" class="Function">large-precategory-Full-Large-Subprecategory</a>
    <a id="874" class="Symbol">(</a> <a id="876" href="group-theory.precategory-of-semigroups.html#469" class="Function">Semigroup-Large-Precategory</a><a id="903" class="Symbol">)</a>
    <a id="909" class="Symbol">(</a> <a id="911" href="group-theory.precategory-of-groups.html#535" class="Function">Group-Full-Large-Subprecategory</a><a id="942" class="Symbol">)</a>
</pre>
### The small precategories of groups

<pre class="Agda"><a id="Group-Precategory"></a><a id="996" href="group-theory.precategory-of-groups.html#996" class="Function">Group-Precategory</a> <a id="1014" class="Symbol">:</a> <a id="1016" class="Symbol">(</a><a id="1017" href="group-theory.precategory-of-groups.html#1017" class="Bound">l</a> <a id="1019" class="Symbol">:</a> <a id="1021" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1026" class="Symbol">)</a> <a id="1028" class="Symbol">→</a> <a id="1030" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="1042" class="Symbol">(</a><a id="1043" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1048" href="group-theory.precategory-of-groups.html#1017" class="Bound">l</a><a id="1049" class="Symbol">)</a> <a id="1051" href="group-theory.precategory-of-groups.html#1017" class="Bound">l</a>
<a id="1053" href="group-theory.precategory-of-groups.html#996" class="Function">Group-Precategory</a> <a id="1071" class="Symbol">=</a> <a id="1073" href="category-theory.large-precategories.html#6110" class="Function">precategory-Large-Precategory</a> <a id="1103" href="group-theory.precategory-of-groups.html#743" class="Function">Group-Large-Precategory</a>
</pre>