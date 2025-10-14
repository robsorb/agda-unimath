# Synthetic category theory

<pre class="Agda"><a id="38" class="Symbol">{-#</a> <a id="42" class="Keyword">OPTIONS</a> <a id="50" class="Pragma">--guardedness</a> <a id="64" class="Symbol">#-}</a>
</pre>
## Idea

Synthetic category theory is an approach to the foundation of mathematics in
which the principal objects are ∞-categories. The theory is due to Cisinski et
al. {{#cite Cisinski24}}, which we will follow here closely. Synthetic category
theory differs from [wild category theory](wild-category-theory.md) in the sense
that wild categories are defined as structured objects, i.e., their definition
follows an "analytic" approach, whereas synthetic categories are defined by the
rules for the type of all synthetic categories.

Some core principles of higher category theory include:

- To express that two things are equal we specify an isomorphism between them.
- Any valid statement or construction in category theory must respect
  isomorphisms {{#cite Makkai98}}.

## Modules in the synthetic category theory namespace

<pre class="Agda"><a id="912" class="Keyword">module</a> <a id="919" href="synthetic-category-theory.html" class="Module">synthetic-category-theory</a> <a id="945" class="Keyword">where</a>

<a id="952" class="Keyword">open</a> <a id="957" class="Keyword">import</a> <a id="964" href="synthetic-category-theory.cone-diagrams-synthetic-categories.html" class="Module">synthetic-category-theory.cone-diagrams-synthetic-categories</a> <a id="1025" class="Keyword">public</a>
<a id="1032" class="Keyword">open</a> <a id="1037" class="Keyword">import</a> <a id="1044" href="synthetic-category-theory.cospans-synthetic-categories.html" class="Module">synthetic-category-theory.cospans-synthetic-categories</a> <a id="1099" class="Keyword">public</a>
<a id="1106" class="Keyword">open</a> <a id="1111" class="Keyword">import</a> <a id="1118" href="synthetic-category-theory.equivalences-synthetic-categories.html" class="Module">synthetic-category-theory.equivalences-synthetic-categories</a> <a id="1178" class="Keyword">public</a>
<a id="1185" class="Keyword">open</a> <a id="1190" class="Keyword">import</a> <a id="1197" href="synthetic-category-theory.invertible-functors-synthetic-categories.html" class="Module">synthetic-category-theory.invertible-functors-synthetic-categories</a> <a id="1264" class="Keyword">public</a>
<a id="1271" class="Keyword">open</a> <a id="1276" class="Keyword">import</a> <a id="1283" href="synthetic-category-theory.pullbacks-synthetic-categories.html" class="Module">synthetic-category-theory.pullbacks-synthetic-categories</a> <a id="1340" class="Keyword">public</a>
<a id="1347" class="Keyword">open</a> <a id="1352" class="Keyword">import</a> <a id="1359" href="synthetic-category-theory.retractions-synthetic-categories.html" class="Module">synthetic-category-theory.retractions-synthetic-categories</a> <a id="1418" class="Keyword">public</a>
<a id="1425" class="Keyword">open</a> <a id="1430" class="Keyword">import</a> <a id="1437" href="synthetic-category-theory.sections-synthetic-categories.html" class="Module">synthetic-category-theory.sections-synthetic-categories</a> <a id="1493" class="Keyword">public</a>
<a id="1500" class="Keyword">open</a> <a id="1505" class="Keyword">import</a> <a id="1512" href="synthetic-category-theory.synthetic-categories.html" class="Module">synthetic-category-theory.synthetic-categories</a> <a id="1559" class="Keyword">public</a>
</pre>
## References

{{#bibliography}}
