-- https://wiki.haskell.org/99_questions/1_to_10

-- run with:
-- $ runhaskell prob01_10.hs
-- or
-- ghci> :load prob01_10.hs
-- ghci> :main

-- prob1 --
myLast :: [a] -> a
myLast [] = error "last of empty list!"
myLast [x] = x
myLast (x:xs) = myLast xs

-- prob2 --
myButLast :: [a] -> a
myButLast [] = error "error"
myButLast [x] = error "error"
myButLast (x:y:[]) = x
myButLast (x:y:xs) = myButLast (y:xs)

-- prob3 --
elementAt :: [a] -> Int -> a
elementAt (x:xs) 1 = x
elementAt (x:xs) i = elementAt xs (i-1)

-- prob4 --
myLength' :: [a] -> Int -> Int
myLength' [] y = y
myLength' (x:xs) y = myLength' xs y+1

myLength :: [a] -> Int
myLength x = myLength' x 0

-- prob5 --
myReverse' :: [a] -> [a] -> [a]
myReverse' [] y = y
myReverse' (x:xs) y = myReverse' xs y++[x] -- TIL: cons only works at beginning of list

myReverse :: [a] -> [a]
myReverse x = myReverse' x []

-- prob6 --
isPalindrome :: Eq a => [a] -> Bool -- TIL: class constraint, a must be in Eq, else == won't work
isPalindrome [] = True
isPalindrome [x] = True
isPalindrome x = head x == last x && isPalindrome (init (tail x))

-- prob7 --
data NestedList a = Elem a | List [NestedList a]
-- TIL: type sig names TYPE, pattern matching names CONSTRUCTOR
flatten :: NestedList a -> [a]
flatten (Elem x) = [x]
flatten (List []) = []
flatten (List x) = foldr1 (++) [flatten k | k <- x]

-- prob8 --
compress :: Eq a => [a] -> [a]
compress [] = []
compress (x:y:[])
    | (x == y) = [x]
    | otherwise = [x,y]
compress (x:y:xs)
    | (x == y) = compress(x:xs)
    | otherwise = x:compress(y:xs)

-- prob9 --
-- ['a', 'a', 'a', 'a', 'b', 'b', 'c', 'd'] -> ['a', 'a', 'a', 'a'], [b', 'b', 'c', 'd']
runsplit :: Eq a => [a] -> ([a], [a])
runsplit (x:xs) =
    | (x == head xs) = (x ++ consec xs
    | otherwise = x

pack :: Eq a => [a] -> [a]


main = do
    print (myLast [1,2,3])
    print (myButLast ['a', 'b', 'c'])
    print (myButLast [1,2,3,4])
    print (myButLast ['a'..'z'])
    print (elementAt [1,2,3] 2)
    print (elementAt "haskell" 5)
    print (myLength [123, 456, 789])
    print (myLength "Hello, world!")
    print (myReverse "A man, a plan, a canal, panama!")
    print (myReverse [1,2,3,4])
    print (isPalindrome [1,2,3])
    print (isPalindrome "madamimadam")
    print (isPalindrome [1,2,4,8,16,8,4,2,1])
    print (flatten (Elem 5))
    print (flatten (List [Elem 1, List [Elem 2, List [Elem 3, Elem 4], Elem 5]]))
    print (flatten (List []) :: [Int])
    print ([] :: [Int])
    print (compress "aaaabccaadeeee")
