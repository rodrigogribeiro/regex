\documentclass{beamer}

\usepackage{amsmath,amssymb}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{graphicx}
\usepackage{tikz}
\usetikzlibrary{trees}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt


\title{Certified Bit-Coded Regular Expression Parsing} 

\author{\textbf{Rodrigo Ribeiro}\inst{1} \and Andr\'e Rauber Du Bois\inst{2}} 
\institute 
{
\inst{1} Departament of Computer Science\\
         Universidade Federal de Ouro Preto \\ $\,$ \\
\inst{2} Departament of Computer Science\\
         Universidade Federal de Pelotas
}
\date{\today}



\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\C{" a "}"

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}
\newcommand{\sembrack}[1]{\ensuremath{\llbracket #1 \rrbracket}}

%subst comment a = "\orange{\texttt{--" a "}}"

%format . = "."
%format Set = "\D{Set}"
%format Set0 = Set "_{\D{0}}"
%format Set1 = Set "_{\D{1}}"
%format List = "\D{List}"
%format [] = "\C{\lbrack\:\rbrack}"
%format , = "\red{,}\,"
%format Nat = "\D{\mathbb{N}}"
%format zero = "\C{zero}"
%format succ = "\C{suc}"
%format id = "\F{id}"
%format o = "\F{\circ}"
%format Vec = "\D{Vec}"
%format :: = "\C{::}"
%format _::_ = "\C{\_::\_}"
%format head = "\F{head}"
%format _==_ = "\D{\_" == "\_}"
%format == = "\D{\equiv}"
%format refl = "\C{refl}"
%format proj₁ = "\F{\pi_1}"
%format proj₂ = "\F{\pi_2}"
%format _UU_ = "\D{\_\lor\_}"
%format UU = "\D{\lor}"
%format left = "\C{left}"
%format right = "\C{right}"
%format Regex = "\D{Regex}"
%format Eps = "\C{\epsilon}"
%format Emp = "\C{\emptyset}"
%format # = "\C{\$}"
%format * = "\C{\bullet}"
%format + = "\C{+}"
%format ⋆ = "\C{\star}"
%format #_ = "\C{\$\_}"
%format _*_ = "\C{\_\bullet\_}"
%format _+_ = "\C{\_+\_}"
%format _** = "\C{\_\star}"
%format ** = "\C{\star}"
%format Char = "\D{Char}"
%format _<<-[[_]] = "\D{\_\in\llbracket\_\rrbracket}"
%format <<-[[ = "\D{\in\llbracket}"
%format ]] = "\D{\rrbracket}"
%format ∅ = "\C{\emptyset}"
%format # = "\C{\$}"
%format ∙ = "\C{∙}"
%format + = "\C{+}"
%format ⋆ = "\C{\star}"
%format #_ = "\C{\$\_}"
%format _∙_ = "\C{\_∙\_}"
%format _+_ = "\C{\_+\_}"
%format _⋆ = "\C{\_\star}"
%format _<<-[[_]] = "\D{\_\in\llbracket\_\rrbracket}"
%format <<-[[ = "\D{\in\llbracket}"
%format ]] = "\D{\rrbracket}"
%format ++ = "\F{++}"
%format => = "\C{\Rightarrow}"
%format _+L_ = "\C{\_+L\_}"
%format _+R_ = "\C{\_+R\_}"
%format +L = "\C{+L}"
%format +R = "\C{+R}"
%format Tree = "\D{Tree}"
%format inl = "\C{inl}"
%format inr = "\C{inr}"
%format star[] = "\C{star[]}"
%format star-:: = "\C{star-::}"
%format flat = "\F{flat}"
%format unflat = "\F{unflat}"
%format exts = "\C{\exists}"
%format forall = "\C{\forall}" 
%format ++ = "\F{++}"
%format IsBitCodeOf = "\D{IsCode}"
%format _IsBitCodeOf_ = "\D{\_IsCode\_}"
%format Bit = "\D{Bit}"
%format one = "\C{1_b}"
%format inl = "\C{inl}"
%format inr = "\C{inr}"
%format star[] = "\C{star[]}"
%format star-:: = "\C{star-::}"
%format decode' = "\F{decode}"
%format code = "\F{code}"
%format BitRegex = "\D{BitRegex}"
%format empty = "\C{empty}"
%format eps = "\C{eps}"
%format char = "\C{char}"
%format choice = "\C{choice}"
%format cat = "\C{cat}"
%format star = "\C{star}"
%format internalize = "\F{internalize}"
%format fuse = "\F{fuse}"
%format erase = "\F{erase}"
%format _<<-<<_>> = "\D{\_\in\langle\_\rangle}"
%format <<-<< = "\D{\in\langle}"
%format >> = "\D{\rangle}"
%format nuu[_] = "\F{\nu[\_]}"
%format nuu[ = "\F{\nu[ }"
%format ]> = "\F{]}"
%format ∈+-invert = "\F{∈+-invert}"
%format []∈∙-invert = "\F{[]∈∙-invert}"
%format ∂[_,_] = "\F{\partial[\_,\_]}"
%format ∂[ = "\F{\partial[}"
%format =?= = "\F{\overset{?}{=}}"
%format mkEps = "\F{mkEps}"
%format IsPrefix = "\D{IsPrefix}"
%format Prefix = "\C{Prefix}"
%format IsSubstring = "\D{IsSubstr}"
%format Substring = "\C{Substr}"

\begin{document}

   \begin{frame}
      \titlepage 
   \end{frame}

   \begin{frame}{Introduction}
     \begin{itemize}
       \item Parsing is pervasive in computing
       \begin{itemize}
          \item String search tools, lexical analysers...
          \item Binary data files like images, videos ...
       \end{itemize}
       \item Our focus: Regular Languages (RLs)
       \begin{itemize}
         \item Languages denoted by Regular Expressions (REs) and
               equivalent formalisms
       \end{itemize}
     \end{itemize}
   \end{frame}

   \begin{frame}{Introduction}
     \begin{itemize}
       \item Is RE parsing a yes / no question?.
       \begin{itemize}
         \item No! Better to produce evidence: parse trees.
       \end{itemize}
       \item Why use bit-codes for parse trees?
       \begin{itemize}
         \item Memory compact representation of parsing evidence.
         \item Easy serialization of parsing results.
       \end{itemize}
     \end{itemize}
   \end{frame}

   \begin{frame}{Contributions}
     \begin{itemize}
       \item We provide fully certified proofs of a derivative based algorithm that
             produces a bit representation of a parse tree.
       \item We mechanize results about the relation between RE parse trees and
             bit-codes.
       \item We provide sound and complete decision procedures for prefix and substring
             matching of RE.
       \item Coded included in a RE search tool developed by us --- verigrep.
       \item All results formalized in Agda version 2.5.2.
     \end{itemize}
   \end{frame}

%   \begin{frame}{An Overview of Agda}
%     \begin{itemize}
%       \item Agda is a dependently typed language based on MLTT.
%       \item Has a Haskell like syntax.
%       \item ``Hello world'' for dependent types:  length indexed lists.
%     \end{itemize}
%     \begin{spec}
%       data Vec (A : Set) : Nat -> Set where
%         []  : Vec A zero
%         _::_ : forall {n} -> A -> Vec A n -> Vec A (succ n)
% 
%       head : Vec A (succ n) -> A
%       head (x :: xs) = x
%     \end{spec}
%   \end{frame}

%format zero = "\C{0_b}"

   \begin{frame}{Regular Expression Syntax}
     \begin{itemize}
       \item Definition of RE over a finite alphabet $\Sigma$.
     \end{itemize}
     \[
     e ::= \emptyset\,\mid\,\epsilon\,\mid\,a\,\mid\,e\,e\,\mid\,e+e\,\mid\,e^{\star}
     \]
     \begin{itemize}
       \item Agda code
     \end{itemize}
     \begin{spec}
     data Regex : Set where
       Emp : Regex
       Eps : Regex
       #_  : Char -> Regex
       _*_ : Regex -> Regex -> Regex
       _+_ : Regex -> Regex -> Regex
       _**  : Regex -> Regex
       \end{spec}
   \end{frame}

   \begin{frame}{Regular Expression Semantics}
   \[
     \Large{
       \begin{array}{cc}
         \infer[]{\epsilon \in \sembrack{\epsilon}}{} &
         \infer[]{a \in \sembrack{a}}{a \in \Sigma} \\ \\
         \infer[]{ss' \in \sembrack{ee'}}
                 {s \in \sembrack{e} & s' \in \sembrack{e'}} &
         \infer[]{s \in \sembrack{e + e'}}{s\in\sembrack{e}}\\ \\
         \infer[]{s' \in \sembrack{e + e'}}{s'\in\sembrack{e'}} &
         \infer[]{s\in \sembrack{e^{\star}}}
                 {s\in\sembrack{\epsilon + ee^{\star}}}
       \end{array}}
   \]
   \end{frame}

   \begin{frame}{Regular Expression Semantics --- Agda code}
     \Large{
       \begin{spec}
         data _<<-[[_]] : List Char -> Regex -> Set where
           Eps  : [] <<-[[ Eps ]]
           #_   : (c : Char) -> # c <<-[[ # c ]]
           _*_  : s <<-[[ l ]]  ->
                  s' <<-[[ r ]]  ->
                  (s ++ s') <<-[[ l * r ]]
           _+L_ : s <<-[[ l ]] -> s <<-[[ l + r ]]
           -- some code omitted...
       \end{spec}}
   \end{frame}

   \begin{frame}{Parse trees for REs}
     \begin{itemize}
       \item We interpret RE as types and parse tree as terms.
       \item Informally:
       \begin{itemize}
         \item leafs: empty string and character.
         \item concatenation: pair of parse trees.
         \item choice: just the branch of chosen RE.
         \item Kleene star: list of parse trees.
       \end{itemize}
     \end{itemize}
   \end{frame}

   \begin{frame}{Parse trees for RE --- Example}
     \begin{figure}
       \begin{tikzpicture}
         [              level 1/.style={sibling distance=10em},
                        level 2/.style={sibling distance=10em},
                        level 3/.style={sibling distance=5em},
                        level 4/.style={sibling distance=5em}]
         \node{|star-::|}
             child{
               node{|inr|}
               child{
                 node{|*|}
                   child {node{|# a|}}
                   child {node{|# b|}}
               }
             }
             child{node{|star-::|}
               child{
                 node{|inr|}
                 child{
                   node{|*|}
                   child {node{|# a|}}
                   child {node{|# b|}}
                 }
               }
               child{node{|star[]|}}
               };
       \end{tikzpicture}
       \centering
       \caption{Parse tree for RE: $(c + ab)^\star$ and the string $w = abab$.}
     \end{figure}
   \end{frame}

\begin{frame}{Parse trees for REs}
  \Large{
    \begin{spec}
      data Tree : Regex -> Set where
        Eps : Tree Eps
        #_ : (c : Char) -> Tree (# c)
        inl : Tree l -> Tree (l + r)
        inr : Tree r -> Tree (l + r)
        _*_ : Tree l -> Tree r -> Tree (l * r)
        star[] : Tree (l **)
        star-:: : Tree l -> Tree (l **) -> Tree (l **)
    \end{spec}}
\end{frame}


   \begin{frame}{Relating parse trees and RE semantics}
     \begin{itemize}
       \item Using function |flat|.
       \item Property: Let $t$ be a parse tree for a RE $e$ and a string s. Then, $flat(t) = s$ and $s \in \sembrack{e}$. 
     \end{itemize}
     \[
        \begin{array}{lcl}
          flat(|Eps|)          & = & [] \\
          flat(|# a|)          & = & [ |a| ] \\
          flat(|inl t|)        & = & flat(|t|)\\
          flat(|inr t|)        & = & flat(|t|)\\
          flat(|t * t'|)       & = & flat(|t|) |++| flat(|t'|) \\
          flat(|star[]|)       & = & [] \\
          flat(|star-:: t ts|) & = & flat(|t|) |++| flat(ts)\\
        \end{array}
     \]
   \end{frame}

   \begin{frame}{Relating parse trees and RE semantics}
     \begin{itemize}
       \item |flat| type ensure its correctness property!  
     \end{itemize}
     \begin{spec}
       flat : Tree e -> exts (\ xs -> xs <<-[[ e ]])
       flat Eps = [] , Eps
       flat (# c) =  [ c ] , (# c)
       flat (inl r t) with flat t
       ...| xs , prf = _ , r +L prf
       flat (inr l t) with flat t
       ...| xs , prf = _ , l +R prf
       flat (t * t') with flat t | flat t'
       ...| xs , prf | ys , prf' = _ , (prf * prf')
       -- some code omitted
     \end{spec}
   \end{frame}

   \begin{frame}{Bit-codes for parse trees}
     \begin{itemize}
       \item Bit-codes mark...
       \begin{itemize}
         \item which branch of choice was chosen during parsing.
         \item matchings done by the Kleene star operator.
       \end{itemize}
       \item Predicate relating bit-codes to its RE.
     \end{itemize}
     \begin{spec}
       data _IsBitCodeOf_ : List Bit -> Regex -> Set where
         Eps : [] IsBitCodeOf Eps
         #_ : (c : Char) -> [] IsBitCodeOf (# c)
         inl : xs IsBitCodeOf l -> (zero :: xs) IsBitCodeOf (l + r)
         inr : xs IsBitCodeOf r -> (one :: xs) IsBitCodeOf (l + r)
         _*_ : xs IsBitCodeOf l -> ys IsBitCodeOf r -> (xs ++ ys) IsBitCodeOf (l * r)
         star[] : [ one ] IsBitCodeOf (l **)
         star-:: : xs IsBitCodeOf l -> xss IsBitCodeOf (l **) -> 
                   (zero :: xs ++ xss) IsBitCodeOf (l **)
     \end{spec}
   \end{frame}

   \begin{frame}{How to relate bit-codes and parse trees?}
     \begin{itemize}
       \item Function |code| builds bit-codes for parse trees.
     \end{itemize}
     \begin{spec}
       code : Tree e -> exts (\ bs -> bs IsBitCodeOf e)
       code (# c) = [] , (# c)
       code (inl r t) with code t
       ...| ys , pr = zero :: ys , inl r pr
       code (inr l t) with code t
       ...| ys , pr = one :: ys , inr l pr
       code star[] = one :: [] , star[]
       code (star-:: t ts) with code t | code ts
       ...| xs , pr | xss , prs = (zero :: xs ++ xss) , star-:: pr prs
       -- some code omitted
     \end{spec}
   \end{frame}

   \begin{frame}{How to relate bit-codes and parse-trees?}
     \begin{itemize}
       \item Function |decode'| parses a bit string for w.r.t. a RE.
       \item Property: forall |t|, |decode' (code t) == t|
     \end{itemize}
     \begin{spec}
       decode' : exts (\ bs -> bs IsBitCodeOf e) -> Tree e
       decode' (_ , (# c)) = # c
       decode' (_ , (inl r pr)) = inl r (decode' (_ , pr))
       decode' (_ , (inr l pr)) = inr l (decode' (_ , pr))
       decode' star[] = (_ +L Eps) **
       decode' (star-:: pr pr') with decode' (_ ,pr) | decode' (_ ,pr') 
       ...| pr1 | pr2 =  (_ +R (pr1 * pr2)) **
       -- some code omitted
     \end{spec}
   \end{frame}

   \begin{frame}{Bit-codes for RE parse trees}
     \begin{itemize}
       \item Building a parse tree for compute bit-codes is expansive.
       \item Better idea: build bit-codes during parsing, instead of computing parse trees.
       \item How? Just attach bit-codes to RE.
     \end{itemize}
     \begin{spec}
       data BitRegex : Set where
         empty  : BitRegex
         eps    : List Bit -> BitRegex
         char   : List Bit -> Char -> BitRegex
         choice : List Bit -> BitRegex -> BitRegex -> BitRegex
         cat    : List Bit -> BitRegex -> BitRegex -> BitRegex
         star   : List Bit -> BitRegex -> BitRegex
     \end{spec}
   \end{frame}

   \begin{frame}{Relating REs and BREs}
     \begin{itemize}
       \item Function |internalize| converts a RE into a BRE. 
     \end{itemize}
     \begin{spec}
       internalize : Regex -> BitRegex
       internalize Emp = empty
       internalize Eps = eps [] 
       internalize (# x) = char [] x
       internalize (e * e') = cat [] (internalize e) (internalize e')
       internalize (e + e') 
         = choice [] (fuse [ zero ] (internalize e)) 
                     (fuse [ one ] (internalize e'))
       internalize (e **) = star [] (internalize e)
     \end{spec}
   \end{frame}

   \begin{frame}{Relating REs and BREs}
     \begin{itemize}
       \item Function |erase| converts a BRE into a RE.
       \item Property: for all |e|, |erase (internalize e) == e|.
     \end{itemize}
     \begin{spec}
       erase : BitRegex -> Regex
       erase empty = Emp
       erase (eps x) = Eps
       erase (char x c) = # c
       erase (choice x e e') = erase e + (erase e')
       erase (cat x e e') = erase e * (erase e')
       erase (star x e) = (erase e) **
     \end{spec}
   \end{frame}

   \begin{frame}{Semantics of BREs}
     \begin{itemize}
       \item Same as RE semantics, but includes the bit-codes.
       \item Property: |s <<-[[ e ]]| iff |s <<-<< internalize e >>|.
     \end{itemize}
     \begin{spec}
       data _<<-<<_>> : List Char -> BitRegex -> Set where
         eps  : [] <<-<< eps bs >>
         char : (c : Char) -> [ c ] <<-<< char bs c >>
         inl  : s <<-<< l >> -> s <<-<< choice bs l r >>
         inr  : s <<-<< r >> -> s <<-<< choice bs l r >>
         cat  : s <<-<< l >> -> s' <<-<< r >> -> (s ++ s') <<-<< cat bs l r >>
         -- some code omitted
     \end{spec}
   \end{frame}

   \begin{frame}{Derivatives in a nutshell}
     \begin{itemize}
       \item What is the derivative of an (B)RE?
       \begin{itemize}
         \item Derivatives are defined w.r.t. an alphabet symbol.
       \end{itemize}
       \item The derivative of a (B)RE $e$ w.r.t. $a$, $\partial(e,a)$, is another (B)RE that denotes
             all strings in $e$ language with the leading $a$ removed.
     \end{itemize}
     \[
     \begin{array}{lclr}
       \partial_a(e) & = & \{ s \mid as \in \sembrack{e} \}\\
     \end{array}
     \]
     \begin{itemize}
       \item Property: | s <<-<< ∂[ e , x ]> >> | holds iff |(x :: s) <<-<< e >> | holds.
     \end{itemize}
   \end{frame}

   \begin{frame}{Derivatives for BREs}
     \begin{itemize}
       \item Follows the definition of Brzozowski's derivatives.
     \end{itemize}
     \begin{spec}
       ∂[_,_] : BitRegex -> Char -> BitRegex
       ∂[ eps bs , c ]> = eps bs
       ∂[ cat bs e e' , c ]> with nuu[ e ]>
       ∂[ cat bs e e' , c ]> | yes pr 
         = choice bs (cat bs ∂[ e , c ]> e') (fuse (mkEps pr) ∂[ e' , c ]>)
       ∂[ cat bs e e' , c ]> | no ¬pr = cat bs ∂[ e , c ]> e'
       ∂[ star bs e , c ]> 
         = cat bs (fuse [ zero ] ∂[ e , c ]>) (star [] e)
       -- some code omitted
     \end{spec}
   \end{frame}

   \begin{frame}{Nullability test for BREs}
     \begin{itemize}
       \item Checks if $\epsilon \in \sembrack{e}$, for some (B)RE e.
       \item Agda code: decision procedure for |[] <<-<< e >>|.
     \end{itemize}
                    \[
                     \begin{array}{lcl}
                          \nu(\emptyset) & = & \emptyset \\
                          \nu(\epsilon)    & = & \epsilon \\
                          \nu(a)                & = & \emptyset \\
                          \nu(e\,e')           & = & \left\{
                                                                  \begin{array}{ll}
                                                                       \epsilon &
                                                                                  \text{if
                                                                                  }\nu(e)
                                                                                  =
                                                                                  \nu(e')
                                                                                  =
                                                                                  \epsilon
                                                                    \\
                                                                    \emptyset &
                                                                                \text{otherwise}
                                                                  \end{array}
                                                              \right. \\
                          \nu(e + e')  & = & \left\{
                                                          \begin{array}{ll}
                                                               \epsilon & \text{if
                                                                          }\nu(e) =
                                                                          \epsilon
                                                                          \text{ or
                                                                          }\nu(e') =
                                                                          \epsilon \\
                                                               \emptyset & \text{otherwise}
                                                          \end{array}
                                                       \right. \\
                          \nu(e^\star) & = & \epsilon
                     \end{array}
                 \]
   \end{frame}

   \begin{frame}{Parsing with derivatives}
     \begin{itemize}
       \item RE-based text search tools parse prefixes and substrings.
       \item Types |IsPrefix| and |IsSubstring| are proofs that a string is
             a prefix / substring of an input BRE.
       \item Parsing algorithms defined as proofs of decidability of |IsPrefix|
             and |IsSubstring|. Proof by induction on the input string, using
             properties of derivative operation.
     \end{itemize}
     \begin{spec}
       data IsPrefix (a : List Char)(e : BitRegex) : Set where
         Prefix : a == b ++ c -> b <<-<< e >> -> IsPrefix a e

       data IsSubstring (a : List Char)(e : BitRegex) : Set where
         Substring :  a == b ++ c ++ d -> c <<-<< e >> -> IsSubstring a e
     \end{spec}
   \end{frame}

   \begin{frame}{Experimental Results}
     \begin{figure}[!ht]
       \includegraphics[width=0.9\textwidth]{as.png}
       \centering
       \caption{Results of experiment 1.}
       \label{fig:graph1}
     \end{figure}
   \end{frame}

   \begin{frame}{Future Work}
     \begin{itemize}
       \item How to improve efficiency?
       \begin{itemize}
         \item How intrinsic verification affects generated code efficiency?
         \item Currently porting code to use extrinsic verification (proofs separated from program code).
         \item Experiment with alternative formalization: BRE semantics defined by |erase|:
               |s <<-<< e >> = s <<-[[ erase e ]]|.
       \end{itemize}
       \item How to measure memory consumption, without compiler support?
       \begin{itemize}
         \item No profiling support in Agda compiler.
         \item Agda compiles to Haskell, but there's no direct correspondence between
               Agda source code and Haskell generated code.
       \end{itemize}
     \end{itemize}
   \end{frame}

   \begin{frame}{Conclusion}
     \begin{itemize}
       \item We build a certified algorithm for BRE parsing in Agda.
       \item We certify several previous results about bit-coded parse trees and
             their relationship with RE semantics.
       \item Algorithm included in verigrep tool for RE text search.
     \end{itemize}
   \end{frame}

   \begin{frame}{Relating REs and BREs}
     \begin{itemize}
       \item Function |fuse| attach a bit-string into a BRE.
     \end{itemize}
     \begin{spec}
       fuse : List Bit -> BitRegex -> BitRegex
       fuse bs empty = empty
       fuse bs (eps x) = eps (bs ++ x)
       fuse bs (char x c) = char (bs ++ x) c
       fuse bs (choice x e e') = choice (bs ++ x) e e'
       fuse bs (cat x e e') = cat (bs ++ x) e e'
       fuse bs (star x e) = star (bs ++ x) e
     \end{spec}
   \end{frame}

   \begin{frame}{Building bit-codes for $\epsilon$}
     \begin{spec}
       mkEps : [] <<-[[ t ]] -> List Bit
       mkEps (eps bs) = bs
       mkEps (inl br bs pr) = bs ++ mkEps pr
       mkEps (inr bl bs pr) = bs ++ mkEps pr
       mkEps (cat bs pr pr' eq) = bs ++ mkEps pr ++ mkEps pr'
       mkEps (star[] bs) = bs ++ [ one ]
       mkEps (star-:: bs pr pr' x) = bs ++ [ one ]
     \end{spec}
   \end{frame}
   \begin{frame}{Relating parse trees and RE semantics}
     \begin{itemize}
       \item |unflat| builds parse trees out of RE semantics evidence.
       \item Functions |flat| and |unflat| are inverses. 
     \end{itemize}
     \begin{spec}
       unflat : xs <<-[[ e ]] -> Tree e
       unflat Eps = Eps
       unflat (# c) = # c
       unflat (prf * prf') = unflat prf * unflat prf'
       unflat (r +L prf) = inl r (unflat prf)
       unflat (l +R prf) = inr l (unflat prf)
       -- some code omitted
     \end{spec}
   \end{frame}

\end{document}
 
