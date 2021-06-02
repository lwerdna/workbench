-- https://wiki.haskell.org/99_questions/21_to_28

-- prob 21 --
insertAt :: a -> [a] -> Int -> [a]
insertAt elem list idx = take (idx-1) list ++ [elem] ++ drop (idx-1) list

-- prob 22 --
range :: Int -> Int -> [Int]
range a b
    | a > b = []
    | otherwise = [a] ++ range (a+1) b

-- prob 23 --

-- prob 24 --

-- prob 25 --

-- prob 26 --

prependAll :: a -> [[a]] -> [[a]]
prependAll x list = [[x] ++ y | y <- list]

combinations :: Int -> [a] -> [[a]]
combinations 1 list = [[x] | x <- list]
combinations n list = foldr1 (++)
                [prependAll (list !! i) (combinations (n-1) (drop (i+1) list)) | i <- [0..moves]]
                where moves = length list - n

main = do
    print (insertAt 'X' "abcd" 2)
    print (range 4 9)
    print (combinations 3 "abcdef")
