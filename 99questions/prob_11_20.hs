-- https://wiki.haskell.org/99_questions/11_to_20

-- from prob_01_10.hs:

runlength :: Eq a => [a] -> Int
runlength (x:[]) = 1
runlength (x:xs)
    | (x == head xs) = 1 + runlength xs
    | otherwise = 1

slice :: [a] -> Int -> Int -> [a]
slice x i j = take (j-i) (drop i x)

pack :: Eq a => [a] -> [[a]]
pack [] = []
pack x = [slice x 0 rl] ++ pack (slice x rl (length x))
             where rl = runlength x

encode :: Eq a => [a] -> [(Int, a)]
encode list = [(length sublist, sublist !! 0) | sublist <- pack list]

-- prob11 --
data EmElem a = Single a | Multiple Int a deriving (Show)

encodeModifiedTest :: (Int, a) -> EmElem a
encodeModifiedTest (1, a) = Single a
encodeModifiedTest (n, a) = Multiple n a

encodeModified :: Eq a => [a] -> [EmElem a]
encodeModified x = map encodeModifiedTest (encode x)

-- prob12 --
decodeModified :: [EmElem a] -> [a]
decodeModified [] = []
decodeModified (Single x : xs) = [x] ++ decodeModified xs
decodeModified (Multiple n x : xs) = replicate n x ++ decodeModified xs

-- prob13 --
-- do not use helper --
encodeDirect :: Eq a => [a] -> [EmElem a]
encodeDirect [] = []
encodeDirect x
    | (l == 1) = [Single (head x)] ++ encodeDirect (tail x)
    | otherwise = [Multiple l (head x)] ++ encodeDirect (drop l x)
    where l = length (takeWhile (\k -> k==head x) x)

-- prob14 --
dupli :: Eq a => [a] -> [a]
dupli [] = []
dupli x = [head x, head x] ++ dupli (tail x)

-- prob15 --
repli :: Eq a => [a] -> Int -> [a]
repli [] n = []
repli x n = replicate n (head x) ++ repli (tail x) n

-- prob16 --
dropEvery :: [a] -> Int -> [a]
dropEvery x n
    | length x < n = x
    | otherwise = take (n-1) x ++ dropEvery (drop n x) n

-- prob17 --
myTake :: Int -> [a] -> [a]
myTake 0 x = []
myTake n (x:xs) = [x] ++ myTake (n-1) xs

myDrop :: Int -> [a] -> [a]
myDrop 0 x = x
myDrop n (x:xs) = myDrop (n-1) xs

split :: [a] -> Int -> ([a], [a])
split x n = (myTake n x, myDrop n x)

-- prob18 --
-- this one is 1-indexed --
slice2 :: [a] -> Int -> Int -> [a]
slice2 x i j = take (j-i+1) (drop (i-1) x)

-- prob19 --
rotate :: [a] -> Int -> [a]
rotate x n
    | n > 0 = drop n x ++ take n x
    | n < 0 = drop n' x ++ take n' x
    where n' = length x + n

-- prob20 --
removeAt :: Int -> [a] -> (a, [a])
removeAt n x = (x !! (n-1), take (n-1) x ++ drop n x)

main = do
    print (encodeModified "aaaabccaadeeee")
    print (decodeModified [Multiple 4 'a',Single 'b',Multiple 2 'c', Multiple 2 'a',Single 'd',Multiple 4 'e'])
    print (encodeDirect "aaaabccaadeeee")
    print (dupli [1,2,3])
    print (repli "abc" 3)
    print (split "abcdefghijk" 3)
    print (slice2 ['a','b','c','d','e','f','g','h','i','k'] 3 7)
    print (rotate ['a','b','c','d','e','f','g','h'] (-2))
    print (rotate ['a','b','c','d','e','f','g','h'] 3)
    print (removeAt 2 "abcd")
