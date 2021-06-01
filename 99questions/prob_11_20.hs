-- https://wiki.haskell.org/99_questions/10_to_20

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

main = do
    print (encodeModified "aaaabccaadeeee") 
