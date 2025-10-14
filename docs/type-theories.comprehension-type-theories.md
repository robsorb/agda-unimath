# Comprehension of fibered type theories

<pre class="Agda"><a id="51" class="Symbol">{-#</a> <a id="55" class="Keyword">OPTIONS</a> <a id="63" class="Pragma">--guardedness</a> <a id="77" class="Symbol">#-}</a>

<a id="82" class="Keyword">module</a> <a id="89" href="type-theories.comprehension-type-theories.html" class="Module">type-theories.comprehension-type-theories</a> <a id="131" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda">
</pre>
</details>

## Idea

Given a fibered type theory `S` over `T`, we can form the comprehension type
theory `∫ST` analogous to the Grothendieck construction.

## Definition

<pre class="Agda"><a id="372" class="Comment">{-
record comprehension
  {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
  {B : fibered.fibered-type-theory l3 l4 A} : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type : {!!}
    element : {!!}
    slice : {!!}
-}</a>
</pre>