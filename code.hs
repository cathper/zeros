-- References are to
--     http://arxiv.org/abs/0912.1436
-- or
--     http://zeros.spag.dk
import List

-- Note the ordering of the lists:
-- [i_m, ..., i_1], [s_m, ..., s_1], [u_1, ..., u_r]

-- sumMult [a_1, ..., a_n] = \sum_{i=1}^n i a_i
sumMult = sum . zipWith (*) [1..]

-- maximize f [a_1, ..., a_n] = max{f(a_1), ..., f(a_n)}
maximize f = maximum . map f

-- Given a list [s1, ..., sn] produce
-- [ [x1, ..., xn] | x1 <- [0..s1], ..., xn <- [0..sn] ].
cartesian :: [Integer] -> [[Integer]]
cartesian = mapM (\n -> [0..n])

cart dim size = cartesian (take (fromInteger dim) (repeat (fromInteger size)))

-- Check if the i vector is outside the stairs form.
-- See Remark 12.
outside :: [Integer] -> Integer -> [Integer] -> Bool
outside is r ss = r <= sum (zipWith div is ss)

-- See Definition 10 and Theorem 11.
d :: [Integer] -> Integer -> [Integer] -> Integer
d is r ss | outside is r ss = product ss
          | otherwise       = dr (reverse is) r (reverse ss)
    where
    dr [i] r [s] = min (i `div` r) s
    dr (i:is) r (s:ss) = maximize f (setA i r s)
        where
            f us = (s - sum us) * (dr is r ss)
                   + summing us is r ss
            -- Note that [u_1, ..., u_r].
            summing [u] is 1 ss = u * product ss
            summing (u:us) is r ss = u * (dr is (r-1) ss)
                                     + summing us is (r-1) ss

-- See Definition 10.
setA :: Integer -> Integer -> Integer -> [[Integer]]
setA i r s = filter (\u -> sum u <= s && sumMult u <= i)
                    (cart r s)

-- d' [i_1, ..., i_m] r q = d [i_1, ..., i_m] r [q, ..., q]
d' :: [Integer] -> Integer -> Integer -> Integer
d' is r q = d is r (replicate (length is) q)

-- See Proposition 39.
htilde :: [[Integer]] -> Integer -> [Integer] -> Integer
htilde ws k ss = hr (reverse ws) k (reverse ss)
    where
    -- [s_m, ..., s_2, s_1]
    -- [w_m, ..., w_2, w_1] = [[v^m_1, ..., v^m_r], ..., [v^1_1, ..., v^1_r]]
    hr [vs] k [s] = sum $ drop (fromIntegral (k-1)) vs
    hr (w:ws) k (s:ss) = (s - (sum w)) * (hr ws k ss)
                          + summing (take (fromIntegral (k-1)) w) k
                          + (sum (drop (fromIntegral (k-1)) w)) * (product ss)
        where
            summing [] 1 = 0
            summing (v:vs) k' = v * (hr ws (k'-1) ss)
                                + summing vs (k'-1)
    hr [] k s = fromIntegral (40 + length s)

-- Lower Bound, H. See Proposition 40.
h :: [Integer] -> Integer -> [Integer] -> Integer
h is r ss = maximize (\ws -> htilde ws r ss) (sequence (set is ss))
    where
        set [] [] = []
        set (i:is) (s:ss) =
            (filter (\vs -> sum vs <= s && sumMult vs == i) (cart r s))
            : set is ss

-- h' [i_1, ..., i_m] r q = h [i_1, ..., i_m] r [q, ..., q]
h' :: [Integer] -> Integer -> Integer -> Integer
h' is r q = h is r (replicate (length is) q)

-- See Corollary 9.
-- min { (i_1·s_1···s_m + s_1·i_2·s_3···s_m + ··· + s_1···s_{m-1}·i_m) / r
--       , s_1···s_m }
sz :: [Integer] -> Integer -> [Integer] -> Integer
sz is r ss = min cor9 (product ss)
    where
        cor9 = (sum (zipWith (*) is (map product $ f ss))) `div` r
        f [] = []
        f (x:xs) = xs : map (x:) (f xs)

-- sz' [i_1, ..., i_m] r q
-- = min{floor((i_1 + ... + i_m) * q^(m-1) / r), q^m}
-- See (2.1).
sz' :: [Integer] -> Integer -> Integer -> Integer
sz' is r q = min (((sum is) * q^(m-1)) `div` r) (q^m)
    where m = length is

-- Closed Formula; two variables.
cf :: [Integer] -> Integer -> [Integer] -> Integer
cf is r ss = truncate (cfrat is r ss)

cf' :: [Integer] -> Integer -> Integer -> Integer
cf' is r q = truncate (cfrat is r [q,q])

-- See Proposition 19.
cfrat :: [Integer] -> Integer -> [Integer] -> Rational
cfrat [i_i1,i_i2] i_r [i_s1,i_s2] =
    minimum (l c1 ++ l c2 ++ l c3 ++ [c4])
    where
        i1 = fromIntegral i_i1; i2 = fromIntegral i_i2
        r = fromIntegral i_r
        s1 = fromIntegral i_s1; s2 = fromIntegral i_s2
        l c = map c [1..r-1]
        c1 k = if (r-k)*(r/(r+1))*s1 <= i1 && i1 < (r-k)*s1
                  && 0 <= i2 && i2 < k*s2
                   then s2*(i1/r) + (i2/r)*(i1/(r-k))
                   else s1*s2
        c2 k = if (r-k)*(r/(r+1))*s1 <= i1 && i1 < (r-k)*s1
                  && k*s2 <= i2 && i2 < (k+1)*s2
                   then s2*(i1/r)
                        + ((k+1)*s2 - i2) * ((i1/(r-k))-(i1/r))
                        + (i2-k*s2)*(s1-(i1/r))
                   else s1*s2
        c3 k = if (r-k-1)*s1 <= i1 && i1 < (r-k)*(r/(r+1))*s1
                  && 0 <= i2 && i2 < (k+1)*s2
                   then s2*(i1/r) + (i2/(k+1))*(s1-(i1/r))
                   else s1*s2
        c4 = if s1*(r-1) <= i1 && i1 < s1*r
                && 0 <= i2 && i2 < s2
                 then s2*(fromIntegral (floor (i1/r)))
                      + i2*(s1 - fromIntegral ( floor (i1/r)))
                 else s1*s2
