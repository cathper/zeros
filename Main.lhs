% To run in ghci or compile with ghc, do just as normal.
% To typeset with LaTeX: lhs2TeX -o Main.tex Main.lhs && pdflatex Main.tex

\documentclass{report}
%include polycode.fmt
%%include lhs2TeX.fmt

\usepackage{graphicx}
\usepackage[draft]{fixme}
\usepackage{amsmath}
\usepackage{bbm}
\usepackage{url}
\usepackage{tikz}

% Move to 
%\usepackage{xr}
%\externaldocument{thesis}
%\usepackage{varioref}
\newcommand{\ref}[1]{\texttt{#1}}
\newcommand{\vref}[1]{\texttt{#1}}

\renewcommand{\v}[1]{{\boldsymbol #1}} % Vector
\newcommand{\N}{\mathbbm{N}} % Natural numbers
\newcommand{\Oh}{\mathcal{O}} % Big Oh.
\newcommand{\F}{\mathbbm{F}} % Field
\newcommand{\floor}[1]{\lfloor{#1}\rfloor}
\begin{document}
\appendix
\addtocounter{chapter}{3}
\chapter{Program Code}

\section{Introduction}

The following is a literate Haskell program. We refer to
\url{http://haskell.org} for reference. As a short note, Haskell is a statically
typed, lazy, purely functional programming language; this makes it very
``math-like'' since we use recursion rather than any kind of loops, have no
destructive updates, handle infinite lists etc.  The syntax is minimal, in the
sense that a function $f(x) = x^2$ is written in Haskell as |f x = x^2| using
Donald E.\ Knuth's up-arrow notation for exponentiation in this text.

Notice that a few lines of code included here is not part of the program but are
included to give explanations; the very first line of code is an example of a
code line comment.

\section{Preliminaries}

% import Control.Parallel
% Might be necessary to do: cabal install parallel
% main = mapM_ print $ parMap parTraversable (\[r,z] -> (r,z,ec_hyper r [8,128] z)) (sequence [[1..13],[42]])

%For use later (to implement |powerset|) we import
%
%> import Control.Monad (filterM)

> import Data.List (nubBy)

\fixme{Udkommentér nubBy.}

Sometimes it is convenient (especially in the process of writing the program and
debugging phase) to be able to make some assertions. Therefore,

> import Control.Exception (assert)

was used while programming.  They can be removed when compiling with @ghc@ by
using @-O[0,2]@ or the explicit @-fignore-asserts@. The following, however, is a
tiny bit faster:

< assert _ x = x


\section{Toolbox}
Given two lists |a| and |x|, |after a x| is true if $a_k \le x_k$ for all $k$.
Written for use of currying/mapping.
%after [a] [x] = a <= x
%after (a:as) (x:xs) = a <= x && after as xs

> after [a1,a2] [x1,x2] = a1 <= x1 && a2 <= x2
> after [a1,a2,a3] [x1,x2,x3] = a1 <= x1 && a2 <= x2 && a3 <= x3
> after a x = and $ zipWith (<=) a x

Here, a version where a list of ``vectors'' can be given and the variable must
be after at least one of the ``vectors'' in the list.

> afterOne l x = or [ after e x | e <- l]

We will at some point think of removing elements from a list rather than
filtering the list, therefore:

> remove f = filter (not . f)

Having the list representing the set $\{ \v v \in \N^m : v_1 \le s_1, \dotsc,
v_m \le s_m \}$ will become handy.

% cart sizes = sequence $ map (\s -> [0..s]) sizes

> cart sizes = mapM (enumFromTo 0) sizes
> cart' dim size = cart $ replicateI dim size

The Cartesian product $l_1 \times \dotsb \times l_n$ is |sequence
[|$l_1,\dotsc,l_n$|]|, and |mapM f xs = sequence (map f xs)|.

Since we want |Integer|s,

> replicateI :: (Integral a, Integral b) => a -> b -> [Integer]
> replicateI a b = replicate (fromIntegral a) (fromIntegral b)

The function |Data.List.intersect| in the standard library is $\Oh(m n)$ where
$m$ and $n$ are the lengths of the two lists to be intersected. This is simply
because the function operates on lists of |Eq|'s. When having lists of |Ord|'s,
one can do intersections faster by first sorting and then using the following
intersection function. The function is found in |Data.List.Ordered|
(@data-ordlist@) by Leon P.\ Smith.

> isect :: Ord a => [a] -> [a] -> [a]
> isect [] _ = []
> isect _ [] = []
> isect (a:as) (b:bs) = assert (sorted (a:as) && sorted (b:bs)) $
>     case compare a b of
>         LT -> isect as (b:bs)
>         EQ -> a : isect as bs
>         GT -> isect (a:as) bs

Similarly, to remove duplicate elements in a list, |Data.List.nub| is $\Oh(n^2)$
whereas it can be done in $\Oh(n)$ using the following strategy also found in
|Data.List.Ordered|:

> nub :: (Ord a) => [a] -> [a]
> nub [] = []
> nub (x:xs) = assert (sorted (x:xs)) (x : loop x xs)
>    where
>    loop x [] = []
>    loop x (y:ys)
>        | x < y     = y : loop y ys
>        | otherwise = loop x ys

% My try at making a list version of intersect. It's thousandfold slower than
% foldr1 isect for a small problem where isect takes ~5 seconds.
% intersect' :: Ord a => [[a]] -> [a]
% intersect' lst
%     | (minimum $ map length lst) == 0 = []
%     | mi == ma                        = ma : intersect' tails
%     | otherwise                       = intersect' $ zipWith (++) heads' tails'
%     where
%     structure = map (splitAt 1) lst
%     heads = map head lst
%     tails = map tail lst
%     (mi,ma) = (minimum heads, maximum heads)
%     heads' = map (filter (==ma) . fst) structure
%     tails' = map snd structure

We, however, construct lists that are sorted rather than sorting just before
using |isect| and |nub|, and just check that the lists are really sorted using
the following simple strategy that is $\Oh(n)$.

> sorted :: (Ord a) => [a] -> Bool
> sorted []       = True
> sorted [a]      = True
> sorted [a,b]    = a <= b
> sorted (a:b:cs) = a <= b && sorted (b:cs)

From time to time we will divide monomials by each other; this corresponds to
subtraction of the exponents.

> [a1,a2] `minus` [b1,b2] = [a1-b1,a2-b2]
> [a1,a2,a3] `minus` [b1,b2,b3] = [a1-b1,a2-b2,a3-b3]
> a `minus` b = assert (length a == length b) (zipWith (-) a b)

Scalar multiplication on the ``set'' of ``monomials''; for instance,
\begin{center}
    |multiply 4 [[1,0,0], [0,3,1]] == [[4,0,0], [0,12,4]]|.
\end{center}

> multiply k ll = map (map (k*)) ll

Binomial coefficient using the recurrence $\binom{n}{k} = \frac{n}{k}
\binom{n-1}{k-1}$:

> binomial :: Integer -> Integer -> Integer
> binomial n 0 = 1
> binomial 0 k = 0
> binomial n k = (binomial (n-1) (k-1)) * n `div` k

The number of monomials in $m$ variables that has degree at most $d$ is, as
shown in Lemma \vref{lem:proof:monomials}, given by

> noOfMonomials :: Integer -> Integer -> Integer
> noOfMonomials vars deg = binomial (vars + deg) (vars)



\section{Upper bound on the number of zeros of given multiplicity}

In this section we shall see the upper bounds found in Chapter \ref{chap:zero}.


\subsection{The bound by $D$}

The function is defined in Definition \vref{def:zero:D} and is shown in Theorem
\ref{thm:zero:D} to give a bound on the number of zeros with multiplicity $\ge
r$ of any polynomial where $\v X^\v i$ is the leading monomial over a set $S_1
\times \dotsb \times S_m$ of sizes $s_1, \dotsc, s_m$.
%Consider optimizing the code according to the last part of Example 18;
%\fixme{reference}
%
%< d is r ss = (d nzis r nzss) * product zss
%<     where
%<     (nzis,nzss) = filter (\(i,_) -> i /= 0) isss
%<     (_,zss) = filter (\(i,_) -> i == 0) isss
%<     isss = zip is ss
%< or
%< d is r ss = (d (fst nz) r (snd nz)) * product (snd z)
%<     where (nz,z) = partition (\(i,_) -> i /= 0) (zip is ss)
%< or the following which is probably not efficient
%< dr (i:is) r (s:ss) | i == 0    = s * (dr is r ss)
%<                    | otherwise = maxim...

> d :: [Integer] -> Integer -> [Integer] -> Integer
> d is r ss
>     | outside is r ss = product ss
>     | otherwise       = dr (reverse is) r (reverse ss)
>     where
>     dr [i] r [s] = min (i `div` r) s
>     dr (i:is) r (s:ss) = maximise f (setA i r s)
>         where
>             f us = (s - sum us) * (dr is r ss) + summing us
>             -- Note that [$u_1, \dotsc, u_r$].
>             summing [u] = u * product ss
>             summing (u:us) = u * (dr is (r-1) ss) + summing us

As noted in Remark \vref{rem:zero:stairs}, there exists a polynomial that has
$s_1 \dotsb s_m$ zeros of multiplicity $\ge r$ if $\floor{i_1/s_1} + \dotsb +
\floor{i_m/s_m} \ge r$. Therefore, the following is used in |d|.

> outside :: [Integer] -> Integer -> [Integer] -> Bool
> outside is r ss = r <= sum (zipWith div is ss)

The following function that maximises functional values over the range of the
input list was used in |d| and is also used in the definition of the function
|h| giving the lower bound (see Section \ref{sec:code:lowerBound}).

> maximise :: (Ord a) => (t -> a) -> [t] -> a
> maximise f = maximum . map f

The first implementation of |setA| would be something like

< setA i r s = filter (\u -> sum u <= s && sumMult u <= i) (cart' r s)

using |sumMult| that calculates $\sum_{l=1}^n l a_l$ as

< sumMult = sum . zipWith (*) [1..]

This first attempt was to construct $\{0, \dotsc, i\}^r$ and then remove the
vectors $\v u$ where $\sum_l u_l > s$ or $\sum_l l u_l > i$. In practice this
turns out to perform badly since the Cartesian product has many more elements
than $A(i,r,s)$, especially for small $i$ or $s$.
When finding $A(i,r,s)$ we should therefore smartly avoid considering vectors
that we know does not fulfill the two conditions for being in $A(i,r,s)$.

\begin{lemma}
    \label{lem:setA}
    In $A'$, let $i$, $r$, and $s$ be implicitly given. Then,
    $A(i,r,s)$ equals
    \begin{equation*}
        \{ \v 0 \} \cup A'(\v 0, 1) \cup \dotsb \cup A'(\v 0, r)
    \end{equation*}
    where
    \begin{equation*}
        A'(\v u, j) = 
        \begin{cases}
            \{ \v u^{(j)} \}
            \cup A'(\v u^{(j)}, j) \cup \dotsb \cup A'(\v u^{(r)}, r)
            ,& \sum_l u^{(j)}_l \le s \ \land\ \sum_l l u^{(j)}_l \le i
            \\
            \emptyset
            ,&\text{otherwise}.
        \end{cases}
    \end{equation*}
    Here, given $\v u = (u_1, \dotsc, u_r)$ we define $\v u^{(j)} =
    (u_1, \dotsc, u_{j-1}, u_j+1, u_{j+1}, \dotsc, u_r) = (u^{(j)}_1, \dotsc,
    u^{(j)}_r)$.
\end{lemma}

\begin{proof}
    We will use induction. The basis step where $(i,r,s) = (0,1,0)$ is trivial.
    Induction on $i$, respectively $s$, applies since $A'(\v u, j)$ adds exactly
    the extra element for given $\v u$ and $j$ when $i+1$, respectively $s+1$,
    is considered. Induction on $r$ applies since $A'(\v 0,r+1)$ adds the
    correct subset of the one dimensional subspace of $\N^{r+r}$.
\end{proof}

This gives the following much faster implementation and has the same (sorted)
output.

> setA :: Integer -> Integer -> Integer -> [[Integer]]
> setA i r s = zero : (concat $ map (worker zero) [1..r])
>     where
>     zero = replicateI r 0
>     worker us index
>         | ok new    = new : (concat $ map (worker new) [index..r])
>         | otherwise = []
>         where
>         new = add1toIndex index us
>         ok mon = sum mon <= s && sumMult mon <= i

This implementation uses the function

> add1toIndex :: Integer -> [Integer] -> [Integer]
> add1toIndex index lst = worker 1 lst
>     where
>     worker k (x:xs)
>         | k < index = x : worker (k+1) xs
>         | otherwise = (x+1) : xs

and also still |sumMult| which can also be made faster:

> sumMult :: [Integer] -> Integer
> sumMult lst = worker 1 lst 0
>     where
>     worker i (a:as) res = worker (i+1) as (res + i*a)
>     worker _   []   res = res

This tail recursive version is a tiny bit faster than the most straight forward
implementation, and since it is run many, many times (as profiling shows), even
tiny runtime improvements as this one adds up.

Just for convenience we have |d'| for the situation where $s_k = q$ for all $k$;
that is, |d' [|$i_1, \dotsc, i_m$|] r q = d [|$i_1, \dotsc, i_m$|] r [|$q,
\dotsc, q$|]|.

> d' :: [Integer] -> Integer -> Integer -> Integer
> d' is r q = d is r (replicate (length is) q)


\subsection{Closed formulae bounds}

Proposition \vref{prop:zero:cf} gives closed formulae upper bounds on $D$; for
some values it is tight, but whereas $D$ gives an integer, the closed formulae
gives a rational number. This covers the case of $m=2$ variables.

> cfrat :: [Integer] -> Integer -> [Integer] -> Rational
> cfrat [i_i1,i_i2] i_r [i_s1,i_s2] =
>     minimum (l c1 ++ l c2 ++ l c3 ++ [c4])
>     where
>         i1 = fromIntegral i_i1; i2 = fromIntegral i_i2
>         r = fromIntegral i_r
>         s1 = fromIntegral i_s1; s2 = fromIntegral i_s2
>         l c = map c [1..r-1]
>         c1 k = if (r-k)*(r/(r+1))*s1 <= i1 && i1 < (r-k)*s1
>                   && 0 <= i2 && i2 < k*s2
>                    then s2*(i1/r) + (i2/r)*(i1/(r-k))
>                    else s1*s2
>         c2 k = if (r-k)*(r/(r+1))*s1 <= i1 && i1 < (r-k)*s1
>                   && k*s2 <= i2 && i2 < (k+1)*s2
>                    then s2*(i1/r)
>                         + ((k+1)*s2 - i2) * ((i1/(r-k))-(i1/r))
>                         + (i2-k*s2)*(s1-(i1/r))
>                    else s1*s2
>         c3 k = if (r-k-1)*s1 <= i1 && i1 < (r-k)*(r/(r+1))*s1
>                   && 0 <= i2 && i2 < (k+1)*s2
>                    then s2*(i1/r) + (i2/(k+1))*(s1-(i1/r))
>                    else s1*s2
>         c4 = if s1*(r-1) <= i1 && i1 < s1*r
>                 && 0 <= i2 && i2 < s2
>                  then s2*(fromIntegral (floor (i1/r)))
>                       + i2*(s1 - fromIntegral (floor (i1/r)))
>                  else s1*s2

The number of zeros is of course an integer, so we simply truncate the rational
number:

> cf :: [Integer] -> Integer -> [Integer] -> Integer
> cf is r ss
>     | length ss == 2 = truncate (cfrat is r ss)
>     | small is r ss  = truncate (cfsmall is r ss)
>     | otherwise      = product ss

Here, in the case of $m>2$ variables we can hope for the exponents to be small
and use Proposition \vref{prop:zero:small}.

> cfsmall :: [Integer] -> Integer -> [Integer] -> Rational
> cfsmall is r ss
>     | small is r ss =
>         (fromIntegral $ product ss) - (product
>             (zipWith (\ik sk ->
>                 (fromIntegral sk) - (fromIntegral ik)/(fromIntegral r))
>                      is ss))

This closed formulae upper bound relies on the $i_k$'s to be small which is
defined in Definition \vref{def:zero:small}:

> small :: [Integer] -> Integer -> [Integer] -> Bool
> small is r ss = a1 && a2 && a3
>     where
>     a1 = and (zipWith (<) (init is) (init ss)) && (last is) <= (last ss)
>     a2 = and [ h (m-2) s l <= h (m-2) l s | l <- [2..r], s <- [1..l-1] ]
>     a3 = and [ h (m-1) s r <= h (m-1) r s | s <- [1..r-1] ]
>     m = length is
>     h len out divisor = (fromIntegral out)
>         * product (zipWith (fun divisor) (take len is) (take len ss))
>     fun = \d ik sk -> (fromIntegral sk) - (fromIntegral ik)/(fromIntegral d)
>           :: Rational

And for convenience,

> cf' :: [Integer] -> Integer -> Integer -> Integer
> cf' is r q = cf is r (replicate (length is) q)


\subsection{Other bounds}

The Schwartz-Zippel bound with multiplicity from Corollary \vref{cor:zero:dvir}
is given by

> sz deg vars mult q = (deg * q^(vars-1)) `div` mult

The Schwartz bound with multiplicity shown by using the proof strategy of Dvir
et al.\ is found in Corollary \vref{cor:zero:dvirGen}. It gives the number
\begin{equation*}
    \min \{ (i_1 s_2 \dotsb s_m + s_1 i_2 s_3 \dotsb s_m + \dotsb + s_1 \dotsb
    s_{m-1} i_m)/r , s_1 \dotsb s_m \}
    .
\end{equation*}

> schwartz :: [Integer] -> Integer -> [Integer] -> Integer
> schwartz is r ss = min cor (product ss)
>     where
>     cor = (sum (zipWith (*) is (map product $ f ss))) `div` r
>     f [] = []
>     f (x:xs) = xs : map (x:) (f xs)

Again, for convenience:

> schwartz' :: [Integer] -> Integer -> Integer -> Integer
> schwartz' is r q = min (sz deg m r q) (q^m)
>     where
>     m = length is
>     deg = sum is


\subsection{Lower bound}
\label{sec:code:lowerBound}

Proposition \vref{prop:zero:H} states that $H$ from Definition \ref{def:zero:H}
is a lower bound on the number of zeros of multiplicity $\ge r$ that a
polynomial with the maximal number of zeros of multiplicity $\ge r$ has.

> h :: [Integer] -> Integer -> [Integer] -> Integer
> h is r ss = maximise (\ws -> htilde ws r ss) (sequence (set is ss))
>     where
>         set [] [] = []
>         set (i:is) (s:ss) =
>             (filter (\vs -> sum vs <= s && sumMult vs == i) (cart' r s))
>             : set is ss

It uses the following function which is from Definition \vref{def:zero:H}.

> htilde :: [[Integer]] -> Integer -> [Integer] -> Integer
> htilde ws k ss = hr (reverse ws) k (reverse ss)
>     where
>     hr [vs] k [s] = sum $ drop (fromIntegral (k-1)) vs
>     hr (w:ws) k (s:ss) =
>         (s - (sum w)) * (hr ws k ss)
>         + summing (take (fromIntegral (k-1)) w) k
>         + (sum (drop (fromIntegral (k-1)) w)) * (product ss)
>         where
>             summing [] 1 = 0
>             summing (v:vs) k' = v * (hr ws (k'-1) ss) + summing vs (k'-1)
>     hr [] k ss = 40 + lengthI ss

Notice that input to |hr| is $[s_m, ..., s_2, s_1]$ and
\begin{equation*}
    [w_m, ..., w_2, w_1] = [[v^m_1, ..., v^m_r], ..., [v^1_1, ..., v^1_r]]
    .
\end{equation*}
Just like we defined |d'| for convenience, we also have |h'|:

> h' :: [Integer] -> Integer -> Integer -> Integer
> h' is r q = h is r (replicate (length is) q)



\section{Finding monomials with few enough zeros}

We will find |[mid,0]| such that |mid| is the largest integer such that
\begin{center}
    |upperBound [mid,0] mult [s1,s2] < e'|.
\end{center}
The |helper| takes care of the boundary conditions whereas |worker| does the
real job of divide and conquer.

> entrance mult [s1,s2] e' = entrance' upperBound mult [s1,s2] e'
> entrance' bound mult [s1,s2] e' = assert (s1 <= s2) helper --L0
>     where
>     s1' = s1*mult-1; s2' = s2*mult-1
>     x1 val = bound [val,0] mult [s1,s2]
>     helper
>         | x1 0   >= e'    = (-1)
>         | x1 (s1'+1) < e' = error "entrance': e' is too large."
>         | x1 s1' <  e'    = s1'
>         | otherwise       = worker 0 s1'
>     worker left right
>         | x1 mid >= e'     = worker left (mid-1) --L1
>         | x1 (mid+1) >= e' = mid --L2
>         | otherwise        = worker (mid+1) right --L3
>         where mid = (left + right) `div` 2 -- floor.

The time consuming part is to calculate the |x1 val|'s if the upper bound is
|d|, otherwise it's pretty cheap.

L0: If not $s_1 \le s_2$, then one should ask for this instead since the
computation time will be potentially lower due to the potentially lower number
of problem divisions in the divide and conquer part (|worker|).
L1: |mid-1| or smaller numbers can be entrance value; |mid|, |mid+1|, ...
cannot.
L2: |mid| is a number that gives few enough zeros and |mid+1| gives too many,
which is exactly the situation we are looking for.
L3: |mid| and |mid+1| both gives few enough zeros, so we can try |mid+1| and
|mid+2|, or even larger neighbours.

We find the set of monomials that is not divisible by any other monomial in the
code.

> corners [] = []
> corners (l:ls)
>     | or $ map (after l) ls = corners ls
>     | otherwise             = l : corners ls

%Now we do the same thing, but by hand without being required to first find all
%of the relevant monomials and then removing the ones that are divisible by other
%monomials. Notice that |cart [1,2]| produces
%\begin{center}
%    [[0,0],[0,1],[0,2],[1,0],[1,1],[1,2]]
%\end{center}
%which is sorted (according to |sorted|). We build the list to conform to this.
%
%> boundary mult ss e' = boundary' upperBound mult ss e'
%> boundary' bound mult [s1,s2] e' =
%>     assert (s1 <= s2) (helper (entrance' bound mult [s1,s2] e') 0)
%>     where
%>     s1' = s1*mult-1; s2' = s2*mult-1
%>     helper x1 x2
%>         | x2 > s2' || x1 < 0              = []
%>         | bound [x1,x2] mult [s1,s2] < e' = helper x1 (x2+1)
%>         | otherwise                       = helper (x1-1) x2 ++ [[x1,x2-1]]
%> boundary' bound mult ss e' = corners $ admissible' bound mult ss e'
%
%Notice that laziness is lost due to the order in which the list is built. The
%same holds for |admissible| below, but this is of no worry since the algorithm
%that uses these functions need the entire list anyway. So no potential
%performance gain due to laziness is lost.

Find the monomials where the upper bound is $< e'$. The two dimensional version
can be generalised; it runs in $\Oh(\log s_1' + s_1' + s_2')$ rather than
$\Oh(s_1' s_2')$.

> admissible :: Integer -> [Integer] -> Integer -> [[Integer]]
> admissible mult ss e' = admissible' upperBound mult ss e'
> admissible' bound mult [s1,s2] e' =
>     assert (s1 <= s2) (addBelow (entrance' bound mult [s1,s2] e') 0)
>     where
>     s1' = s1*mult-1; s2' = s2*mult-1
>     addBelow x1 x2
>         | x2 > s2'   = error "admissible': e' too large."
>         | x1 < 0     = []
>         | zeros < e' = addBelow x1 (x2+1)
>         | otherwise  = addBelow (x1-1) x2 ++ [[x1,b] | b <- [0..x2-1]]
>         where zeros = bound [x1,x2] mult [s1,s2]

For $m=3$ variables the first quite simple approach is the following.

> admissible' bound mult [s1,s2,s3] e' = assert (s1 <= s2) $
>     concat $ takeWhile (not.null)
>         [ map (i1:) $ admissible' (bound' i1 s1) mult [s2,s3] e'
>         | i1 <- [0..mult*s1-1] ]
>     where
>     bound' i1 s1 = \[i2,i3] mult [s2,s3] -> bound [i1,i2,i3] mult [s1,s2,s3]

It is slower than the optimal---$\Oh(s_1 \log s_2)$ can be lowered to
$\Oh(s_1)$---but still way faster then the following very intuitive and general
version.

> admissible' bound mult ss e' = worker $ cart s's
>     where
>     s's = map (\s -> s*mult-1) ss
>     worker [] = []
>     worker (is:iss)
>         | bound is mult ss < e' = is : worker iss
>         | otherwise             = worker $ remove (after is) iss



\section{The number of equations}

The number of equations that is put up by the new decoding algorithm (Algorithm
\vref{alg:codes:decoding}) is $n N(m,r)$ as explained in Section
\ref{sec:codes:decoding}:

> equations :: Integer -> [Integer] -> Integer
> equations mult ss = (product ss) * (noOfMonomials (vars+1) (mult-1))
>     where vars = lengthI ss
>
> equations' :: Integer -> Integer -> Integer -> Integer
> equations' vars mult q = (q^vars) * (noOfMonomials (vars+1) (mult-1))

Here, the following type convenient function is used.

> lengthI :: [a] -> Integer
> lengthI lst = fromIntegral $ length lst


\section{Variables}

The number of variables is the number of monomials $N$ that can be multiplied on
all monomials $M$ in the (border of the) code giving a monomial $MN$ that has
few enough zeros. We still treat monomials $\v X^\v i$ as vectors $\v i$.
Subtraction of vectors is equivalent to division of monomials.

> monomials code mult ss e' = takeWhile (not.null) [worker k | k <- [0..]]
>     where
>     admis = admissible mult ss e'
>     worker 0 = admis
>     worker i = foldr1 isect --L0
>                    $ map factorsOf (multiply i code)
>         where
>         factorsOf p = map (`minus` p) (filter (after p) admis) --L1

L0: Way faster than |foldr1 Data.List.intersect|! The inputs are sorted due to
the the way |admissible| is defined.
L1: |factorsOf p| are those monomials that can be multiplied on $p$ such that
the resulting monomial has few enough zeros.

One could use instead

< monomials code mult ss deg e' = remove null [worker k | k <- [0..h]]

and include

<     h = (maximum (0 : map maximum admis)) `div` deg

defined as the largest $Z$-degree of the polynomial $Q$ from Algorithm
\ref{alg:codes:decoding}.


The following is an implementation of the same functionality as above, but here
the |worker| is made tail recursive with the extra gain that fewer and fewer
monomials should be considered. If the filtering takes time (in the
$\Oh(n)$-world, not because of constants), then the following should be(come)
faster.

> monomials' code mult ss e' = takeWhile (not.null) (worker 0 admis)
>     where
>     admis = admissible mult ss e'
>     worker 0 a = a : worker 1 a
>     worker k a = mons : worker (k+1) a'
>         where
>         frontier = multiply k code
>         a' = filter (afterOne frontier) a
>         mons = foldr1 isect $ map factorsFrom frontier
>         factorsFrom p = map (`minus` p) a'

Notice that |afterOne| uses short circuit, and since $s_1 \le s_2$ (just
exemplifying for two variables), by a property of $D$ and the closed
formulae\footnote{The smaller $s_k$, the sooner $D(...) \ge x$ is reached for
any $x$ because of the ordering of the monomials.} and by the ordering on the
monomials, the number of elements to check is smallest possible.
%
In other words, considering Reed-Muller codes in two variables, the number
of monomials after $\v i$ is less than or equal to the number of monomials after
$\v j$ if $i_1 < j_1$ while $\sum_k i_k = \sum_k j_k$. The reason being that
$s_1 \le s_2$.

Correspondingly, one could use

< monomials' code mult ss deg e' = remove null (worker 0 admis)

and

<     h = (maximum (0 : map maximum admis)) `div` deg
<     worker k a
<         | k > h     = []
<         | otherwise = mons : worker (k+1) a'

% FXME: Product of RS-codes where the degrees are different!

The number of variables is the number of monomials.

> variables code mult ss e' = assert (m == m')
>     sum $ map lengthI $ m --L0
>     where
>         m = monomials code mult ss e'
>         m' = monomials' code mult ss e'

L0: Tests using the closed formulae as the upper bound using @ghc@ version
6.12.3 and options @--make -O2@: Running |ec_wrm [1,2] 8 [45,90] 7| when using
|m'| takes ~50 \% longer to finish than when using |m|.  The same holds for
|ec_wrm [1,2] 8 [45,90] 23|. So the tail recursive |worker| is not faster; at
least for the problem sizes we have considered.



\section{Codes}

In this section we will see functions that generates the codes; and functions
that generates the code borders.


\subsection{Reed-Muller codes}

> rm [s1,s2] deg = corners $ bend [s1,s2] $ zipL [0..deg] (reverse [0..deg])
>     where zipL = zipWith (\a b -> [a,b])
> rm ss deg = corners $ bend ss $ diagonal
>     where
>     diagonal = filter ((deg ==) . sum) (cart' (lengthI ss) deg)

If the total degree of a monomial is larger than or equal to at least one |s|,
then we shall not use the diagonal, but rather the minimum of the border and the
diagonal.
See Figure \ref{fig:bend}: Each gray represents a monomial, for instance the
boxed gray dot represents $X^9 Y^3$. The solid black dots are those that have
total degree at most $10$. The circled dots are the output of |bend| when the
monomials of total degree at most $10$ is bend around $s_1=s_2=8$.
\begin{figure}
    %\includegraphics[width=\textwidth]{bend-example.jpg}
    \centering
    \begin{tikzpicture}
        [x=2em,y=2em,>=latex,
        graydot/.style={circle,fill=gray,inner sep=0pt,minimum size=.375em},
        blackdot/.style={circle,fill=black,inner sep=0pt,minimum size=.375em},
        boxdot/.style={rectangle,draw,inner sep=0pt,minimum size=.525em},
        circledot/.style={circle,draw,inner sep=0pt,minimum size=.525em}]
    \path[use as bounding box] (-1.5,-1.5) rectangle (11,11);
    \draw [->,very thick] (-.5,-.5) node {} -- (11,-.5);
    \draw [->,very thick] (-.5,-.5) node {} -- (-.5,11);
    \foreach \y in {0,...,10}
            \draw (-1,\y) node {$Y^{\y}$};
    \foreach \x in {0,...,10}
            \draw (\x,-1) node {$X^{\x}$};
    \foreach \x in {0,...,10}
        \foreach \y in {0,...,10}
            \draw (\x,\y) node [graydot] {};
    \foreach \x in {0,...,10}
        \foreach \y in {0,...,\x}
            \draw (10-\x,\y) node [blackdot] {};
    \foreach \x in {3,...,7}
        \foreach \y in {3,...,\x}
            \draw (10-\x,\y) node [circledot] {};
    \foreach \x in {0,...,7}
        \foreach \y in {0,...,2}
            \draw (\x,\y) node [circledot] {};
    \foreach \x in {0,...,2}
        \foreach \y in {3,...,7}
            \draw (\x,\y) node [circledot] {};
    \draw (9,3) node [boxdot] {};
    \end{tikzpicture}
    \caption{Illustrating |bend| where monomials in $X,Y$ are bend with
        degree $10$ around $s_1=s_2=8$.}
    \label{fig:bend}
\end{figure}
Notice that |(s:ss)| are the sizes in each direction and |(x:xs)| is just one
single monomial! That is, |bend| bends monomials one by one to the corresponding
one on the border.

> bend ss ms = nub $ sort $ map (worker ss) ms -- |ms| are monomials.
>     where
>     worker [] [] = []
>     worker (s:ss) (i:is)
>         | i >= s = s-1 : worker ss is
>         | i < s  = i : worker ss is

When mapping |worker ss| on a list, the result might have duplicates since two
monomials can be converted to the same, thus the |nub|. Since |nub| needs its
input to be sorted, we sort it.
Notice that |bend| will work on the entire code as well as the border of the
code.

The entire code is

> rm' ss deg = bend ss $ code
>     where
>     code = filter ((<= deg) . sum) (cart' (lengthI ss) deg)

and the dimension is

> rmDim ss deg = lengthI $ rm' ss deg

In the case of $S_1 = \dotsb = S_m = \F_q$ we have the following well-known
closed formula for the dimension of Reed-Muller codes:

> rmDimCFq q m deg =
>     sum [ (-1)^k * (bin m k) * (bin (t - k*q + m - 1) (m - 1))
>         | t <- [0..deg], k <- [0..m] ]

using a version of the binomial coefficient that accounts for negative arguments
by returning zero

> bin n k
>     | n < 0 || k < 0 = 0
>     | otherwise      = binomial n k

In Proposition \vref{prop:codes:rm:dim} we showed that the following
generalisation of the above closed formula gives the dimension of Reed-Muller
codes over any Cartesian product:

> rmDimCF ss deg =
>     sum [ (sign sI) * (bin (t - (sum sI) + m - 1) (m - 1))
>         | t <- [0..deg], sI <- powerset ss]
>     where
>     m = lengthI ss

using the function |sign set| that returns |1| if the cardinality of |set| is
even and |-1| if the cardinality is odd:

> sign set
>     | length set `mod` 2 == 0 = 1
>     | otherwise               = -1

Thanks to List monad we have the following elegant definition of |powerset| that
gives the ``(order preserving) power list'' of the input list:

> powerset :: [a] -> [[a]]
> powerset = filterM (const [True, False])

The minimum distance is given by

> rmMinDist ss deg = minDist (rm' ss deg) ss

utilising the general property from Proposition \vref{prop:codes:ems:minDist}
that

> minDist code ss = minimum [ product (ss `minus` is) | is <- code ]

since the codes contains all monomials below the boarder.

One could also use the closed formula way to calculate the minimum distance of
Reed-Muller codes:

> rmMinDistCF ss deg = assert (deg <= product (map (\s -> s-1) ss))
>     loop deg (sort ss)
>     where
>     loop t (s:ss)
>         | s-1 <= t  = loop (t-(s-1)) ss
>         | otherwise = (s-t) * product ss


\subsection{Weighted Reed-Muller codes}

We continue with weighted Reed-Muller codes where we have some weights $\v w$
and consider the code $\{ \v X^\v i : i_k \le s_k \ \textrm{for all}\ k\
\textrm{and}\ \sum_k w_k p_k \le d\}$.

The boundary of the code is

> wrm weights ss deg = corners $ wrm' weights ss deg

since the code is

> wrm' weights ss deg = bend ss $ triangle
>     where
>     triangle = filter ((<= deg) . (sum . zipWith (*) weights))
>                       (cart' (length ss) deg)

The dimension and minimum distance is simply

> wrmDim weights ss deg = length $ wrm' weights ss deg
> wrmMinDist weights ss deg = minDist (wrm' weights ss deg) ss

In two dimensions, the following weights will give the best code (restricting to
the situation where $s_1 \mid s_2$):

> optimalWeight [s1,s2] deg
>     | s1 > s2             = error "optimalWeight: s1 should be smallest."
>     | s2 `rem` s1 /= 0    = error "optimalWeight: s1 does not divide s2."
>     | deg <= s2-s2`div`s1 = [s2`div`s1,1]
>     | s2-1 <= deg         = [1,1]
>     | (deg+1)`rem`s1 == 0 = [(deg+1)`div`s1,1]
>     | otherwise           = error "optimalWeight: No integer weights."

% weirdWeights [s1,s2] = assert (s1 <= s2)
%     [ (k,[w1 k,1]) | k <- [(s2-s2`div`s1)..(s2-1)] ]
%     where
%     w1 k = s2-k

We can use the optimal weights to generate a weighted Reed-Muller code, so we
do not have to calculate the weights ``by hand''.

> wrm2 [s1,s2] deg = wrm (optimalWeight [s1,s2] deg) [s1,s2] deg
> wrm2' [s1,s2] deg = wrm' (optimalWeight [s1,s2] deg) [s1,s2] deg
> wrm2Dim [s1,s2] deg = lengthI $ wrm2' [s1,s2] deg
> wrm2MinDist [s1,s2] deg = minDist (wrm2' [s1,s2] deg) [s1,s2]

< wrm3' :: [Integer] -> Integer -> [[Integer]]
< wrm3' [s1,s2] deg = bend [s1,s2] $ triangle
<     where
<     triangle = filter (\[i1,i2] -> 1*i1 + (ceiling (sqrt ((fromInteger s2)*(fromInteger s1))/(fromInteger s1)))*i2 <= deg)
<                       (cart [deg,deg])

< wrm3Dim [s1,s2] deg = lengthI $ wrm3' [s1,s2] deg
< wrm3MinDist [s1,s2] deg = minDist (wrm3' [s1,s2] deg) [s1,s2]


% From now, s1 >= s2!

> wrm4' :: [Integer] -> Integer -> [[Integer]]
> wrm4' [s1,s2] deg = bend [s1,s2] $ triangle
>     where
>     triangle = filter (\[i1,i2] -> w1*(fromInteger i1) + w2*(fromInteger i2) <= (fromInteger deg))
>                       (cart [deg,deg])
>     [w1,w2] = optimalWeight2 [s1,s2] deg

> optimalWeight2 :: [Integer] -> Integer -> [Double]
> optimalWeight2 [i_s1,i_s2] i_deg
>     | s1 < s2                               = error "s1 < s2"
>     | 0 <= deg && deg <= s1 - s1/s2         = [1,s1/s2]
>     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = [1,s1-deg]
>     | s1 - s/s2 <= deg && deg <= s1 - 1     = [1,s1-deg]
>     | s1-1 <= deg                           = [1,1]
>     where
>     s = sqrt (s1*s2)
>     s1 = fromInteger i_s1
>     s2 = fromInteger i_s2
>     deg = fromInteger i_deg

> wrm4Dim [s1,s2] deg = lengthI $ wrm4' [s1,s2] deg
> wrm4MinDist [s1,s2] deg = minDist (wrm4' [s1,s2] deg) [s1,s2]


% Back to normal where s1 <= s2.


\subsection{Product of Reed-Solomon codes}

The boundary of the product of Reed-Solomon codes is the monomial in the corner;
the single monomial that all other monomials of the code divides:

> prod :: [Integer] -> [[Integer]]
> prod degs = [map (\d -> d-1) degs]

Note that the definition of the $k$th Reed-Solomon code requires that the
$k$-degree of the monomials must be $< d$ as opposed to Reed-Muller codes where
the condition is $\le d$.

> prodDim :: [Integer] -> Integer
> prodDim degs = product degs

The entire code is

> prod' degs = cart $ map (\d -> d-1) degs

and the minimum distance is

> prodMinDist degs ss = minDist (prod degs) ss


\subsection{Hyperbolic codes}
%The following codes depends on the upper bond |upperBound|. It definitely would
%be possible to consider codes defined using the $D$ function and bounding its
%error correction ability using the closed formulae (or vice versa; however, the
%former is probably the most reasonable thing to do having runtimes of |d| in
%mind).
%
%> hyper bound mult ss z = boundary' bound mult ss z
%
%An alternative definition could be
%
%< hyper bound mult ss z = corners $ admissible' bound mult ss z
%
%which would also work for $s_1 \le s_2$. However we may assume that this is the
%case due to \fixme[inline]{Resultat om at |cf| runder værst op når $s_1 > s_2$;
%sådan må det være.}
%
%|z| as in ``the number of zeros the monomial should have fewer zeros than''.
%
%The entire code, its dimension and its minimum distance is
%
%> hyper' bound mult ss z = admissible' bound mult ss z
%> hyperDim bound mult ss z = length $ hyper' bound mult ss z
%> hyperMinDist bound mult ss z = minDist (hyper' bound mult ss z) ss
%
%If one wants to find the (ordered) |z|'s such that |hyperDim bound mult ss z|
%gives |dim| then one can use the following (naïve) function
%
%> hyperZ bound mult ss dim = loop 0
%>     where
%>     loop z
%>         | d <  dim = loop (z+1)
%>         | d == dim = z : loop (z+1)
%>         | d >  dim = []
%>         where
%>         d = hyperDim bound mult ss z
%>
%> hyperZmin bound mult ss dim = head $ hyperZ bound mult ss dim
%
%|hyperZmin| will fail if no |z|'s will give the prescribed dimension.
%%%%%%%%%
%The following naïve approach turns out to be too slow for large problems; for
%instance it takes a substantial amount of time when $|S_1| = 32$ and $|S_2| =
%1024$.
%
%> hyperZmin ss minDist = head $ hyperZ ss minDist
%
%< hyperZmin ss minDist = helper 0 max???
%<     where
%<     helper l r 
%<         | l == r     = l
%<         | md z < mid = 
%<         where mid = (l + r) `div` 2
%<     md z = hyperMinDist ss z
%
%|hyperZmin| will fail if no |z|'s will give the prescribed minimum distance.

The hyperbolic codes we are now to implement has designed minimum distance $z$;
we refer to Section \vref{sec:codes:hyper}.
Again, as with the weighted Reed-Muller code, the border of the code

> hyper ss z = corners $ hyper' ss z

is implemented using the entire code

> hyper' ss z = filter (\is -> product (ss `minus` is) >= z)
>                      (cart (map (\s -> s-1) ss))

The dimension is due to Proposition \ref{prop:codes:ems:dim} given by

> hyperDim ss z = length $ hyper' ss z

The minimum distance of the hyperbolic code could be calculated by

< hyperMinDist ss z = minDist (hyper' ss z) ss

but it is designed to have the minimum distance |z| so there is really no need
for this function, but for clarity we also include

> hyperMinDist ss z = z


\subsection{The Joyner code}

We refer to Section \vref{sec:codes:joyner}.

> joyner = [0,0] : map (`minus` [0-1,0-1]) (rm' [8,8] (5-2))

> joynerDim = 11
> joynerMinDist = 28


\section{Decoding radius}

We search for the least number of errors $e = \prod_k s_k - e'$ such that there
is not enough variables using a divide and conquer approach and return $e-1$.
This gives the decoding radius, or, the \textbf{e}rror \textbf{c}orrection
capability, of the given code (boundary).

> ec code mult ss
>     | maximum (head code) == 0
>            && length code == 1 = error "Code is only [0,...,0]."
>     | otherwise                = helper 0 (product ss)
>     where
>     helper l r --left and right
>         | l == r    = l-1
>         | ok m      = helper (m+1) r
>         | otherwise = helper l m
>         where m = (l+r) `div` 2 --floor.
>     ok e = variables code mult ss e' > equations mult ss
>         where e' = product ss - e

Notice that the design of the divide and conquer algorithm minimises the number
of times |ok e| will be issued.

For being handy when testing |ec| and inspecting results by hand:

> ok code mult ss e = variables code mult ss e' > equations mult ss
>     where e' = product ss - e

For convenience we have a bunch of functions that constructs the codes and finds
the codes error correction ability.

> ec_rm :: Integer -> [Integer] -> Integer -> Integer
> ec_rm mult ss deg = ec (rm ss deg) mult ss

> ec_wrm :: [Integer] -> Integer -> [Integer] -> Integer -> Integer
> ec_wrm weights mult ss deg = ec (wrm weights ss deg) mult ss

> ec_wrm2 :: Integer -> [Integer] -> Integer -> Integer
> ec_wrm2 mult ss deg = ec (wrm2 ss deg) mult ss

> ec_prod :: Integer -> [Integer] -> [Integer] -> Integer
> ec_prod mult ss degs = ec (prod degs) mult ss

> ec_hyper :: Integer -> [Integer] -> Integer -> Integer
> ec_hyper mult ss z = ec (hyper ss z) mult ss


\subsection{Other decoding radii}

From \cite{pellikaan2004a}:

> pellikaanWu q m deg = floor $ q^m * (1 - sqrt (deg / q))

The following is from \cite{augot2009a}:

> pwAsym s vars deg =
>     floor $ s**vars * (1 - (deg/s)**(1/(vars+1)))**vars

> pw s vars deg mult =
>     floor $ s**vars * (1 - (deg/s * prod)**(1/(vars+1)))**vars
>     where prod = product $ map (\n -> 1+n/mult) [1..vars]

> asAsym s vars deg = floor $ s**vars * (1 - (deg/s)**(1/(vars+1)))

> as s vars deg mult = floor $ s**vars * (1 - (deg/s * prod)**(1/(vars+1)))
>     where prod = product $ map (\n -> 1+n/mult) [1..vars]

The following is from \cite{parvaresh2006a}:

> asProductAsym s vars deg = floor $ s**vars * (1 - (deg/s)**(1/(vars+1)))

> asProduct s vars deg mult =
>     floor $ s**vars * (1 - (deg/s * prod)**(1/(vars+1)))
>     where prod = product $ map (\n -> 1+n/mult) [1..vars]

The following originates from \cite{santhi2007a} with the comments from Section
\vref{sec:codes:subfield}.

> santhi :: [Integer] -> Integer -> Integer -> Integer
> santhi ss q deg = santhi' (fromIntegral $ product ss) q (lengthI ss) deg

> santhi' :: Integer -> Integer -> Integer -> Integer -> Integer
> santhi' n q vars t = max 0 $ floor $
>     (fromIntegral n) *
>     (1 - sqrt ((fromIntegral $ t * q^(vars-1)) / (fromIntegral n)))

> santhi'' n ms q = santhi' n q (lengthI $ head ms) (maximise sum ms)



\section{Main}

An example: Using the closed formulae bound to find the decoding radius of a
hyperbolic code $\{ X_1^{i_1} X_2^{i_2} : (45-i_1)(90-i_2) < 23 \}$ over $S_1
\times S_2$ with $s_1 = 45$ and $s_2 = 90$ when using multiplicity $8$ is done
with the code

< upperBound = cf
< main = print $ ec_hyper 8 [45,90] 23


\section{Sorting lists}

The following function is taken from |Data.List|, it is here for completeness.

> sort :: (Ord a) => [a] -> [a]
> sort = sortBy compare
>
> sortBy :: (a -> a -> Ordering) -> [a] -> [a]
> sortBy cmp = mergeAll . sequences
>   where
>     sequences (a:b:xs)
>       | a `cmp` b == GT = descending b [a]  xs
>       | otherwise       = ascending  b (a:) xs
>     sequences xs = [xs]
>
>     descending a as (b:bs)
>       | a `cmp` b == GT = descending b (a:as) bs
>     descending a as bs  = (a:as): sequences bs
>
>     ascending a as (b:bs)
>       | a `cmp` b /= GT = ascending b (\ys -> as (a:ys)) bs
>     ascending a as bs   = as [a]: sequences bs
>
>     mergeAll [x] = x
>     mergeAll xs  = mergeAll (mergePairs xs)
>
>     mergePairs (a:b:xs) = merge a b: mergePairs xs
>     mergePairs xs       = xs
>
>     merge as@(a:as') bs@(b:bs')
>       | a `cmp` b == GT = b:merge as  bs'
>       | otherwise       = a:merge as' bs
>     merge [] bs         = bs
>     merge as []         = as

\section{Generalised filtering}

For completeness is here also the |filterM| from |Control.Monad|.

> filterM :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
> filterM _ []     = return []
> filterM p (x:xs) = do
>     flg <- p x
>     ys  <- filterM p xs
>     return (if flg then x:ys else ys)


\end{document}

% For hyper:
% main = mapM_ print [(r,z,hyperDim cf r ss z) | r <- mults, z <- zs]

> upperBound = cf

< mults = [3]
< degs  = [1..4]
< minDists = [ rmMinDist ss deg | deg <- degs ]
< ss = [257,257]

< main = do
<     print $ [(r,d,ec_rm r [54,54] d) | d <- [2], r <- [8] ]

< main = do
<     print $ [(r,ec_rm r ss deg) | r <- mults, deg <- degs]


% Til at lave performance plot; først af hyper, så af wrm.

< zs = takeWhile (<144*144)
<      $ map fst
<      $ Data.List.nubBy (\x y -> (snd x) == (snd y))
<                        [ (z,hyper ss z) | z <- [1..] ]
< ss = [144,144]
< main = do
<    print "dim"
<    print $ map (\x -> (fromIntegral x)/(144*144)) [ hyperDim ss z | z <- zs ]
<    print "mindist"
<    print $ map (\x -> (fromIntegral x)/(144*144)) [ hyperMinDist ss z | z <- zs ]

< ss = [144,144]
< main = do
<    print "dim"
<    print $ map (\x -> (fromIntegral x)/(144*144)) $ takeWhile (<144*144) [ wrm4Dim ss deg | deg <- [0..] ]
<    print "mindist"
<    print $ map (\x -> (fromIntegral x)/(144*144)) $ takeWhile (>1) [ wrm4MinDist ss deg | deg <- [0..] ]

< ss = [512,2]
< main = do
<    print "dim"
<    print $ map (\x -> (fromIntegral x)/(32*32)) $ takeWhile (<32*32) [ wrm4Dim ss deg | deg <- [0..] ]
<    print "mindist"
<    print $ map (\x -> (fromIntegral x)/(32*32)) $ takeWhile (>1) [ wrm4MinDist ss deg | deg <- [0..] ]

< ss = [162,128]
< --ss = [192,108]
< --ss = [216,96]
< --ss = [288,72]
< --ss = [576,36]
< --ss = [1152,18]
< --ss = [2592,8]
< main = do
<    print "dim"
<    print $ map (\x -> (fromIntegral x)/(144*144)) $ takeWhile (<144*144) [ wrm4Dim ss deg | deg <- [0..] ]
<    print "mindist"
<    print $ map (\x -> (fromIntegral x)/(144*144)) $ takeWhile (>1) [ wrm4MinDist ss deg | deg <- [0..] ]

%%%%%%%%

< --ss = [144,144]
< --ss = [162,128]
< --ss = [192,108]
< --ss = [216,96]
< ss = [288,72]
< --ss = [576,36]
< --ss = [1152,18]
< --ss = [2592,8]
< main = do
<     print $ dimsCode == dimsCalc
<     print $ mindistCode == mindistCalc
<     where
<     dimsCode = takeWhile (<144*144) [ wrm4Dim ss deg | deg <- degs ss ]
<     dimsCalc = takeWhile (<144*144) [ calcDim ss deg | deg <- degs ss ]
<     mindistCode = takeWhile (>1) [ wrm4MinDist ss deg | deg <- degs ss ]
<     mindistCalc = takeWhile (>1) [ calcMinDist ss deg | deg <- degs ss ]

< degs [s1,s2] = filter (\u -> (u * s2) `rem` s1 == 0 || (fromInteger u) >= (fromInteger s1) - (fromInteger s1)/(fromInteger s2)) [1..]

< calcDim [i_s1,i_s2] i_deg
<     | s1 < s2                               = error "s1 < s2"
<     | 0 <= deg && deg <= s1 - s1/s2         = floor $ (deg^2*s2/s1+deg)/2 + deg*s2/s1 + 1
<     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = floor $ deg*s2^2/2 - s1*s2^2/2 + s1*s2/2 + deg*s2/2 + s2
<     | s1 - s/s2 <= deg && deg <= s1 - 1     = floor $ deg*s2^2/2 - s1*s2^2/2 + s1*s2/2 + deg*s2/2 + s2
<     | s1-1 <= deg                           = error "finish"
<     where
<     s = sqrt (s1*s2)
<     s1 = fromInteger i_s1
<     s2 = fromInteger i_s2
<     deg = fromInteger i_deg

< calcMinDist [i_s1,i_s2] i_deg
<     | s1 < s2                               = error "s1 < s2"
<     | 0 <= deg && deg <= s1 - s1/s2         = floor $ s2*(s1-deg)
<     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = floor $ (s1-deg)*s2
<     | s1 - s/s2 <= deg && deg <= s1 - 1     = floor $ (s1-deg)*s2
<     | s1-1 <= deg                           = error "finish"
<     where
<     s = sqrt (s1*s2)
<     s1 = fromInteger i_s1
<     s2 = fromInteger i_s2
<     deg = fromInteger i_deg


< --ss = [144,144]
< [s1,s2] = [288,72]
< --ss = [1152,18]
< --ss = [2592,8]
< main = do
<     print $ zip dimsCode dimsCalc
<     where
<     dimsCode = takeWhile (<144*144) [ rmDim [s1,s2] (floor $ sqrt ((fromInteger deg)^2*(fromInteger s2)/(fromInteger s1))) | deg <- degs [s1,s2] ]
<     dimsCalc = takeWhile (<144*144) [ calcDim [s1,s2] deg | deg <- degs [s1,s2] ]

< degs [s1,s2] = filter (\u -> (u * s2) `rem` s1 == 0) [1..]

< calcDim [i_s1,i_s2] i_deg
<     | s1 < s2                               = error "s1 < s2"
<     | 0 <= deg && deg <= s1 - s1/s2         = floor $ (s2/s1*deg^2 + 3*deg*(sqrt (s2/s1)) + 2)/2
<--     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = floor $ (s2*deg/s+2)*(s2*deg/s+1)/2
<--     | s1 - s/s2 <= deg && deg <= s1 - 1     = floor $ (
<     | otherwise                             = error "finish"
<     where
<     s = sqrt (s1*s2)
<     s1 = fromInteger i_s1
<     s2 = fromInteger i_s2
<     deg = fromInteger i_deg



> ss = [16,16]
> main = do

>    print "dim"
>    print $ map (\x -> (fromIntegral x)/(16*16)) $ takeWhile (<16*16) [ rmDim ss deg | deg <- [0..] ]
>    print "mindist"
>    print $ map (\x -> (fromIntegral x)/(16*16)) $ takeWhile (>1) [ rmMinDist ss deg | deg <- [0..] ]

<    print "dim"
<    print $ map (\x -> (fromIntegral x)/(16*16)) $ takeWhile (<16*16) [ calcDim ss deg | deg <- [0..] ]
<    print "mindist"
<    print $ map (\x -> (fromIntegral x)/(16*16)) $ takeWhile (>1) [ calcMinDist ss deg | deg <- [0..] ]

> calcDim [i_s1,i_s2] i_deg
>     | s1 < s2                               = error "s1 < s2"
>     | 0 <= deg && deg <= s1 - s1/s2         = floor $ (s2/s1*deg^2 + 3*deg*(sqrt (s2/s1)) + 2)/2
>     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = floor $ (s2*deg/s+2)*(s2*deg/s+1)/2
>     | s1 - s/s2 <= deg && deg <= s1 - 1     = floor $ (s1-deg)*s2*((s1-deg)*s2-1)/2
>     | otherwise                             = 16*16 -- stop!
>     where
>     s = sqrt (s1*s2)
>     s1 = fromInteger i_s1
>     s2 = fromInteger i_s2
>     deg = fromInteger i_deg

> calcMinDist [i_s1,i_s2] i_deg
>     | s1 < s2                               = error "s1 < s2"
>     | 0 <= deg && deg <= s1 - s1/s2         = floor $ s2*(s1-deg)
>     | s1 - s1/s2 <= deg && deg <= s1 - s/s2 = floor $ (s1-deg)*s2
>     | s1 - s/s2 <= deg && deg <= s1 - 1     = floor $ (s1-deg)*s2
>     | s1-1 <= deg                           = 1 -- stop!
>     where
>     s = sqrt (s1*s2)
>     s1 = fromInteger i_s1
>     s2 = fromInteger i_s2
>     deg = fromInteger i_deg



%     putStrLn "(r,deg,bound)"

%     print $ ok (rm [16,16,16] 1) 2 [16,16,16] 17

%     mapM_ print $ [ (r,deg,ec_rm r ss deg) | r <- mults, deg <- degs ]

%     mapM_ print $ [ (r,minDist,ec_hyper r ss (hyperZmin ss minDist)) | r <- mults, minDist <- minDists ]



% main = do
%     putStrLn $ "Running ec on hyper where ss=" ++ show ss
%     putStrLn "(r,minDist,bound)"
%     mapM_ print $ [ (r,minDist,ec_hyper r ss (hyperZmin ss minDist)) | r <- mults, minDist <- minDists ]

% Check if hyper and wrm codes are equal:
% let dims = [1..]; ws = [8,1]; ss = [8,64] in [ hyper ss z == wrm ws ss d | d <- dims | z <- [ wrmMinDist ws ss dim | dim <- dims ] ]
% Requires -XParallelListComp to compile.

% To see what the bounds on the number of zeros are:

< splitEvery :: Int -> [e] -> [[e]]
< splitEvery i ls = map (take i) (build (splitter ls)) where
<     splitter [] _ n = n
<     splitter l c n  = l `c` splitter (drop i l) c n
< chunk = splitEvery

< build g = g (:) []

Example: 

< mapM_ print $ reverse $ chunk (2*8) [ cf is 2 [16,8] | is <- cart [2*16-1,2*8-1] ]

< mapM_ print $ Data.List.transpose $ chunk (2*8) [ cf is 2 [16,8] | is <- cart [2*16-1,2*8-1] ]
< mapM_ print $ chunk (2*16) [ cf is 2 [8,16] | is <- cart [2*8-1,2*16-1] ]
< let a = Data.List.transpose $ chunk (2*8) [ cf is 2 [16,8] | is <- cart [2*16-1,2*8-1] ]
< let b = chunk (2*16) [ cf is 2 [8,16] | is <- cart [2*8-1,2*16-1] ]

> eatEqual [] [] = [(0,0)]
> eatEqual (a:as) (b:bs)
>     | a == b    = eatEqual as bs
>     | otherwise = (a,b) : eatEqual as bs


% Are the codes the same?
% Must be run in ghc with -XParallelListComp

< [ (hyper cf r [64,128] z) == (wrm [2,1] [64,128] 20) | r <- [2,3,4,9,20] | z <- [ hyperZmin cf r [64,128] 121 | r <- [2,3,4,9,20] ] ]



% 
< [ (wrmDim v [64,4] k, wrmMinDist v [64,4] k) | k <- [48..63] | v <- (w [64,4])
]
< [ rmMinDist [16,16] deg | deg <- [12..15] ]
