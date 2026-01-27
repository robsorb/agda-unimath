# Essential fibers of functors between precategories

<pre class="Agda"><a id="63" class="Keyword">module</a> <a id="70" href="category-theory.essential-fibers-of-functors-precategories.html" class="Module">category-theory.essential-fibers-of-functors-precategories</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="236" class="Keyword">open</a> <a id="241" class="Keyword">import</a> <a id="248" href="category-theory.isomorphisms-in-precategories.html" class="Module">category-theory.isomorphisms-in-precategories</a>
<a id="294" class="Keyword">open</a> <a id="299" class="Keyword">import</a> <a id="306" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>

<a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="381" class="Keyword">open</a> <a id="386" class="Keyword">import</a> <a id="393" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
</pre>
</details>

## Idea

Given a [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) and an object `y : D` we can
form the **essential fiber** of `y` over `F` as the
[subprecategory](category-theory.subprecategories.md) of `C` spanned by... TODO

## Definitions

### The essential fiber over an object

<pre class="Agda"><a id="803" class="Keyword">module</a> <a id="810" href="category-theory.essential-fibers-of-functors-precategories.html#810" class="Module">_</a>
  <a id="814" class="Symbol">{</a><a id="815" href="category-theory.essential-fibers-of-functors-precategories.html#815" class="Bound">l1</a> <a id="818" href="category-theory.essential-fibers-of-functors-precategories.html#818" class="Bound">l2</a> <a id="821" href="category-theory.essential-fibers-of-functors-precategories.html#821" class="Bound">l3</a> <a id="824" href="category-theory.essential-fibers-of-functors-precategories.html#824" class="Bound">l4</a> <a id="827" class="Symbol">:</a> <a id="829" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="834" class="Symbol">}</a>
  <a id="838" class="Symbol">(</a><a id="839" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a> <a id="841" class="Symbol">:</a> <a id="843" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="855" href="category-theory.essential-fibers-of-functors-precategories.html#815" class="Bound">l1</a> <a id="858" href="category-theory.essential-fibers-of-functors-precategories.html#818" class="Bound">l2</a><a id="860" class="Symbol">)</a> <a id="862" class="Symbol">(</a><a id="863" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a> <a id="865" class="Symbol">:</a> <a id="867" href="category-theory.precategories.html#3316" class="Function">Precategory</a> <a id="879" href="category-theory.essential-fibers-of-functors-precategories.html#821" class="Bound">l3</a> <a id="882" href="category-theory.essential-fibers-of-functors-precategories.html#824" class="Bound">l4</a><a id="884" class="Symbol">)</a>
  <a id="888" class="Symbol">(</a><a id="889" href="category-theory.essential-fibers-of-functors-precategories.html#889" class="Bound">F</a> <a id="891" class="Symbol">:</a> <a id="893" href="category-theory.functors-precategories.html#3811" class="Function">functor-Precategory</a> <a id="913" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a> <a id="915" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a><a id="916" class="Symbol">)</a>
  <a id="920" class="Keyword">where</a>

  <a id="929" href="category-theory.essential-fibers-of-functors-precategories.html#929" class="Function">essential-fiber-functor-Precategory</a> <a id="965" class="Symbol">:</a> <a id="967" class="Symbol">(</a><a id="968" href="category-theory.essential-fibers-of-functors-precategories.html#968" class="Bound">y</a> <a id="970" class="Symbol">:</a> <a id="972" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="988" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a><a id="989" class="Symbol">)</a> <a id="991" class="Symbol">→</a> <a id="993" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="996" class="Symbol">(</a><a id="997" href="category-theory.essential-fibers-of-functors-precategories.html#815" class="Bound">l1</a> <a id="1000" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1002" href="category-theory.essential-fibers-of-functors-precategories.html#824" class="Bound">l4</a><a id="1004" class="Symbol">)</a>
  <a id="1008" href="category-theory.essential-fibers-of-functors-precategories.html#929" class="Function">essential-fiber-functor-Precategory</a> <a id="1044" href="category-theory.essential-fibers-of-functors-precategories.html#1044" class="Bound">y</a> <a id="1046" class="Symbol">=</a>
    <a id="1052" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1054" class="Symbol">(</a> <a id="1056" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1072" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a><a id="1073" class="Symbol">)</a>
      <a id="1081" class="Symbol">(</a> <a id="1083" class="Symbol">λ</a> <a id="1085" href="category-theory.essential-fibers-of-functors-precategories.html#1085" class="Bound">x</a> <a id="1087" class="Symbol">→</a> <a id="1089" href="category-theory.isomorphisms-in-precategories.html#2238" class="Function">iso-Precategory</a> <a id="1105" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a> <a id="1107" class="Symbol">(</a><a id="1108" href="category-theory.functors-precategories.html#4132" class="Function">obj-functor-Precategory</a> <a id="1132" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a> <a id="1134" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a> <a id="1136" href="category-theory.essential-fibers-of-functors-precategories.html#889" class="Bound">F</a> <a id="1138" href="category-theory.essential-fibers-of-functors-precategories.html#1085" class="Bound">x</a><a id="1139" class="Symbol">)</a> <a id="1141" href="category-theory.essential-fibers-of-functors-precategories.html#1044" class="Bound">y</a><a id="1142" class="Symbol">)</a>

  <a id="1147" href="category-theory.essential-fibers-of-functors-precategories.html#1147" class="Function">essential-fiber-functor-Precategory&#39;</a> <a id="1184" class="Symbol">:</a> <a id="1186" class="Symbol">(</a><a id="1187" href="category-theory.essential-fibers-of-functors-precategories.html#1187" class="Bound">y</a> <a id="1189" class="Symbol">:</a> <a id="1191" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1207" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a><a id="1208" class="Symbol">)</a> <a id="1210" class="Symbol">→</a> <a id="1212" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1215" class="Symbol">(</a><a id="1216" href="category-theory.essential-fibers-of-functors-precategories.html#815" class="Bound">l1</a> <a id="1219" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1221" href="category-theory.essential-fibers-of-functors-precategories.html#824" class="Bound">l4</a><a id="1223" class="Symbol">)</a>
  <a id="1227" href="category-theory.essential-fibers-of-functors-precategories.html#1147" class="Function">essential-fiber-functor-Precategory&#39;</a> <a id="1264" href="category-theory.essential-fibers-of-functors-precategories.html#1264" class="Bound">y</a> <a id="1266" class="Symbol">=</a>
    <a id="1272" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="1274" class="Symbol">(</a> <a id="1276" href="category-theory.precategories.html#4633" class="Function">obj-Precategory</a> <a id="1292" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a><a id="1293" class="Symbol">)</a>
      <a id="1301" class="Symbol">(</a> <a id="1303" class="Symbol">λ</a> <a id="1305" href="category-theory.essential-fibers-of-functors-precategories.html#1305" class="Bound">x</a> <a id="1307" class="Symbol">→</a> <a id="1309" href="category-theory.isomorphisms-in-precategories.html#2238" class="Function">iso-Precategory</a> <a id="1325" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a> <a id="1327" href="category-theory.essential-fibers-of-functors-precategories.html#1264" class="Bound">y</a> <a id="1329" class="Symbol">(</a><a id="1330" href="category-theory.functors-precategories.html#4132" class="Function">obj-functor-Precategory</a> <a id="1354" href="category-theory.essential-fibers-of-functors-precategories.html#839" class="Bound">C</a> <a id="1356" href="category-theory.essential-fibers-of-functors-precategories.html#863" class="Bound">D</a> <a id="1358" href="category-theory.essential-fibers-of-functors-precategories.html#889" class="Bound">F</a> <a id="1360" href="category-theory.essential-fibers-of-functors-precategories.html#1305" class="Bound">x</a><a id="1361" class="Symbol">))</a>
</pre>
## See also

- [Essentially surjective functors between precategories](category-theory.essentially-surjective-functors-precategories.md)
- [Split essentially surjective functors between precategories](category-theory.split-essentially-surjective-functors-precategories.md)

## External links

- [Essential Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibres)
  at 1lab
- [essential fiber](https://ncatlab.org/nlab/show/essential+fiber) at $n$Lab
