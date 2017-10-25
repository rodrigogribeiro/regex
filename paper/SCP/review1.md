Editor Comments

The reviews of this paper are split. We think Reviewer 1's concerns on algorithm specification 
should be addressed for the journal publication. Given that the algorithm is Agda-verified and 
a good portion of definitions have been formalized, a complete specification may not be far. 
We leave the decision on how to proceed with this journal to the authors: if a complete 
specification can fit into the (short) second-round time window, we welcome the authors 
to revise and resubmit this paper.

=========


Reviewer #1:
Summary of the submission:
This work studies derivative-based parsing of regular expressions.
The approach is formalized in Agda and some details are discussed
in the paper.


Analysis of the submission:
p2, l43 Authors claim "A formalization of Brzozowski derivatives based RE parsing in Agda"

  The authors formalize some aspects of derivatives in Agda. But I couldn't find
  a *clearly specified* and certified parsing algorithm in the paper.
  The material presented on pages 17 and 18 seems connected to the claim but
  where's the parsing algorithm including its correctness proof?
  
Answer: We understand that the parsing problem for RE consists in finding all matching prefixes and 
substrings for a given input string and some RE e. In section 4.4, we present types that specify 
when an input string has a prefix / substring that matches some RE and decidability proofs 
for such types.
  
p2, l50 Authors claim "A detailed explanation of the technique used to quotient derivatives with respect to ACUI axioms"

 This is not true! The authors implement a few (simple) identities such as epsilon . r = r

 ACI is not dealt with at all. It's an essential step to guarantee that the number of dissimilar derivatives (under ACI) is finite.
 
Answer: You are right! We removed all references to ACUI axioms and mention explicitly that we use smart constructors to 
simplify RE using some well known equivalences.
  
p3, l13 Authors claim "A formalization of Antimirov's derivatives ..."

 The authors use lists to represent the set of *partial* derivatives. Yet again, I(demptotence) is simply dropped.
 Antimirov uses a smart constructor to simplify epsilon . r to r, it's only a minor detail, but again
 something which the authors didn't discuss.
 
Answer: We didn't mention Antimirov simplification step because we are already using it for Brzozowski derivatives.
        Also, such simplification step doesn't affect correctness of the Antimirov partial derivative based parsing
        algorithm.

The authors report poor performance result. This is no surprise as the size of derivatives and partial derivatives
will explode because the authors formalization doesn't simplify derivatives based on ACI
and the list representation used for partial derivatives contains duplicates.

Answer: The number of derivatives is only relevant when one is building a finite state machine from a given RE.
Quotienting resulting REs under ACUI guarantees the finite number of dissimilar derivatives ensuring termination
of the automata construction. For parsing, simplyfing under all axioms of ACUI isn't necessary since the number
of dissimilar derivatives is irrelevant, because termination of RE derivative based parsing depends on the 
size of the input string not on the number of derivatives of a given RE.

Minor comments

p3, l13     Antimorov's *partial* derivatives

Answer: Fixed.

p8, l14    "...inversion lemmas...", at least provide some details, otherwise, the reader is left clueless

Answer: We have added the inversion lemma for choice and single character RE and some text explaining these definitions.

agda instead of Agda, various places
 
Answer: Fixed. 


Recommendations:
I recommend to reject this work.

- The contributions are not significant enough. In fact, the contributions claimed
 at the beginning of the paper are not substantiated at all.
 
Answer: We appreciate Reviewer #1 detailed comments which allowed us to fix and improve the presentation of our work. 
We believe that the text is now consistent, and that we have properly addressed the main concerns of Reviewer #1:
   * We remove the references to ACUI axioms, since they aren't needed for RE derivative based parsing. Also 
     we explicitly mention that smart-constructors only perform simplifications based on simple RE equivalences.
   * We have added some examples of RE semantics relation, Brzozowski derivatives, Antimirov partial derivatives 
     and parsing using derivatives. 

- The structure can be improved (mainly a boring sequences of Agda formalization and results).
 I couldn't find a single worked out example!
 
Answer: We added examples of Brzozowski derivatives and Antimirov's partial derivatives.  


Reviewer #2: The paper presents a formalization of Brzozowski and Artimov derivatives for regular expression parsing. The derivatives are an alternative method for the description of parsing algorithms for recognizing regular languages. The formalization is developed in Agda, a dependently-typed functional language. The paper extends SBLP'16 paper by the addition of a formalization of Artimov derivatives.

The paper presents an interesting application of the use of a language with dependent types for the development of certfied algorithms. The formalization in Agda seems reasonable. In most cases the Agda representations closely follow the structure of the formal concepts that are being modeled. Surely, this fact is the origin of some of the performance penalties (as mentioned by the authors).

The paper is clear and in general well-written. 

Answer: Thank you!

Typos and specific comments are given below.

Specific comments:

page 2)
l. 33: until his work -> until their work (or it is _his_ work because there you are referring to Brzozowski?)

Answer: Fixed. 

l. 34: interest on its use -> interest on their use

Answer: Fixed.

l. 39: that has been developed by us, using -> we developed by using

Answer: Fixed.

page 3)
l. 13: derivatives and its use -> derivatives and their use

Answer: Fixed.

page 4)
l. 14: of types of types -> of types

Answer: Fixed.

1st paragraph: Seems unnecessary to speak about the stratification of types

page 5)
l. 42: Dec p -> Dec P

Answer: Fixed.

page 6)
l. 36: suc -> S

Answer: Fixed.

page 7)
l. 12: In our Agda formalization, *in contrast*, we represent....

Answer: Fixed.

l. 31: Bigger -> Composite

Answer: Fixed.

l. 36: constructor*s* specifies

Answer: Fixed.

In the definition of RE semantics:
perhaps  mention that in Agda one can overload constructor names. 

Answer: We add the following sentences before the definition of RE semantics data type:
"Agda allows the overloading of constructor names. In some cases we use the same symbol for 
the RE syntax and its underlying semantics."

l. 42: $c -> [c] (outside the double brackets)

Answer: Fixed.

l. 43: Is it neccesary to define zs? couldn't you directly say xs++ys \in [[l \bullet r]], instead of zs = xs++ys -> zs \in [[l \bullet r]]?

Answer: It is possible to define the semantics of concatenation without mention zs. We introduce this extra equality because it simplifies
some proofs.  

l. 53: Simply for uniformity, perhaps you can speak about character c instead of a in order to use the same name as in the data definition.

Answer: Fixed.

page 8)
l. 9: from a parse tree from l (r) -> from a parse tree for l (r)

Answer: Fixed.

In section 4, perhaps it is useful if you present examples of derivatives

Answer: We added examples of derivatives and partial derivatives.

l. 47: is proved by function \nu[e] -> is proved by function \nu[_]

Answer: Fixed.

page 9)
l. 29: RE's -> REs

Answer: Fixed.

l. 35: [8], we use smart -> [8]. We use smart

Answer: Fixed.

Mention somewhere that smart constructors are denoted by prefixing a back quote to the constructor name.

Answer: Before the definitions of the smart constructors we put the following sentence:
"As a convention, we name smart constructors by 
prefixing a back quote to the constructor name."

page 10+11)
Instead of stating 6 different lemmas, I would join the soundness lemmas in only one with cases as 1, 2 and 3 (and a proof for each case), and the same with the completeness lemmas.

Answer: We simplify the presentation by joining soundness and completeness lemmas for each of the smart constructors.

page 10)
l. 32: one of the REs are -> one of the REs is

Answer: Fixed.

page 12)
l. 17: a RE with respect -> a RE e with respect

Answer: Fixed.

The definition of \delta in the case \delta_a(e e') deserves some explanation

page 13)
l. 40: (section title) and its Properties -> and their Properties

Answer: Fixed.

Explain in what sense Antimirov's derivatives are "partial"

l. 48: collectively accepts -> collectively accept

Answer: Fixed.

l. 50: ACUI equations holds -> ACUI equations hold

page 14)
l. 30: agda -> Agda

Answer: Fixed.

There is a mismatch in the order of the parameters between Agda's definition of \odot and the formal definition of \odot in line 28 (S \odot e').

Answer: Fixed.

page 16)
l. 21: theorems -> theorem

Answer: Fixed.

l. 50: encode -> encodes

Answer: Fixed.

page 17)
From the explanation on page 16 about what "matching a prefix" and "matching a substring" mean one would expect that 
the definitions of those concepts are given by sigma types. Perhaps it would be helpful to mention that the GADTs 
provided in fact express such existentials.

Answer: We add a sentence explaining that such predicates (prefix and substring) could be easily defined by dependent products.
We choose to define new types for clarity.

In the definition of constructor String of IsSubstring a (\forall (ys zs ws)) is missed.

Answer: We omit such parameters to avoid clutter. In Section 2, we have:
"To avoid clutter, we’ll omit implicit arguments from the source code presentation. The reader can safely assume that every free variable in a type is an implicity parameter."

page 18)
l. 9: better refer to Lemma 13

Answer: Fixed.

l. 31: e -> xs

Answer: Fixed.

page 19)
l. 54: 'be' appears twice
l. 54: the Brzozowski definition -> Brzozowski's definition

Answer: Fixed.

page 21)
l. 50: drop a '.'

Answer: Fixed.

l. 57: \cite missed (\cite{Norell2009})

Answer: Fixed.

page 22)
l. 9: a lot -> much

Answer: Fixed.

l. 22: CFG -> a CFG

Answer: Fixed.

l. 45: shows -> show

Answer: Fixed.

page 23)
l. 11: have given -> gave

Answer: Fixed.

About the references:
- A section name ("References") needs to be added.

Answer: Fixed.

- Except for those that need the URLs, I would eliminate URL and doi information from most references

- References [5] and [25] are the same.

Answer: Fixed.

- Reference [12] is the SBLP 2016 paper, isn't it? Year is 2016 and should say SBLP instead of Programming Languages.

Answer: We cited the book chapter on LNCS 9889 which consists of the proceedings for SBLP 2016. 


Reviewer #3: The paper describes a mechanized formalization (in Agda) of two approaches
to regular expression parsing using derivatives, along with
proofs of soundness for the two approaches. The first uses Brzozowski
derivatives and the second Antimorov's derivatives. The first one
has already been covered in the conference version of the paper,
but the second one is novel. The result is a provably-sound algorithm
for regular expression parsing, which the authors used to build a grep-like
tool and evaluated the performance of this tool against similar tools.

The paper is long but not hard to follow, but is is dry and needs
to explain things better to the reader that does not know either Agda
or regular expression derivatives.

For example, I had to go look up "indexed datatypes" in an Agda tutorial
to understand the N -> Set and A -> Set parts in the data definitions of Vec
and equality on pages 4 and 5. It seems that the text has been kept from
the previous version of the paper, that used Idris for the mechanization,
but the notation that Idris use is more explicit. In the definition of Dec,
shouldn't the lowercase p in the type of "no" be an uppercase P?

Answer: Yes! We fixed the lower case p in the definition of Dec type.

The section on "smart constructors" could be greatly shortened. They are
not essential to the correctness of the derivative parsing algorithm,
just for performance, and the identities and accompanying lemmas are
very simple.

Answer: We joined the soundness and completeness lemmas for each smart constructor to
reduce the description of such functions.

On the other hand, the explanation about Brzozowski derivatives could
be expanded with a concrete example of why they are interesting for
regular expression parsing.

Answer: We modify the sections on Brzozowski derivatives, Antimirov partial derivatives 
and parsing by adding examples and explaining how to use derivatives for parsing.

The definition of Antimirov's derivatives is using the symbol for
the Brzozowski derivative in the right side of concatenation.

Answer: Yes, fixed!

In the experiments, I find it odd that re2, grep, and even haskell-regexp
in several parts os exhibiting constant-time behavior while the input
increases, while regular expression parsing using automata, as well
as using derivatives, is linear in the length of the input (and the
implementation in the paper shows roughly linear behavior). Perhaps
the choice of very simple regular expressions is making the more
mature implementations "optimize away" the "regular expression"
part.

My recommendation is to accept after minor revisions, basically to
better explain both the use of Agda and an informal explanation of why
derivatives of regular expressions work and why they are interesting
for parsing. The experimental results also need better analysis, as
I am not convinced that the two reasons they gave tell the whole story;
the other implementations should be better by a constant factor, but
with the exception of haskell-regexp they are exhibiting better asymptotic
behavior.

Answer: Thank you for your careful reading. We extended the text in order
to better explain (partial) derivatives and their use
for parsing and examples of these concepts. We also add some explanation about
indexed and parameterized data types in Section 2.