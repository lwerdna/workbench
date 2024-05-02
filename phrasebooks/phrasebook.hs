----------
-- GHCI --
----------
-- :type
-- :info <func> gives precedence, associativity (left vs. right)
-- precedence ranges from low (eg: $ has 0) to high (eg: funct application 10)

-- function as infix operator: `function`
1 `elem` [1,2,3] -- True
-- infix operator as function: (operator)
(+) 1 2 -- 3
-- composition
let fn = f . g . h
let fn x = f (g (h x)) -- same
(f . g . h) x otherwise 

fn x -- the "invisible juxtaposition function application" operator, has highest precedence (binds tightest)
f g h = ((f g) h) -- function application operator is left-associative


-- don't have to include argument name (point-free vs. pointful)
-- https://wiki.haskell.org/Pointfree (vs. pointful)

-----------
-- LISTS --
-----------
-- https://wiki.haskell.org/How_to_work_on_lists

-- operators --
[1,2,3] ++ [4,5,6] -- concat, [1,2,3,4,5,6]
1:[2,3] -- cons(truct), [1,2,3]
[1,2,3,4] !! 2 -- dereference 2nd (0-indexed) element, 3
[1,2,3] < [2,2,3] -- compare (element-wise), True

head [1,2,3,4] -- 1
last [1,2,3,4] -- 4

init [1,2,3,4] -- [1,2,3]
tail [1,2,3,4] -- [2,3,4]

take 3 [1,2,3,4] -- [1,2,3]
drop 3 [1,2,3,4] -- 4

takeWhile
dropWhile

null [1,2,3,4] -- check empty, False
elem 1 [1,2,3,4,5] -- check membership, True

splitAt 5 [1,2,3,4,5] -- ([1,2,3,4,5],[6,7])

-- infinite lists --
replicate 5 'a' -- ['a','a','a','a','a'] finite length
repeat [1] -- [1,1,1,...]
cycle [1,2,3] -- [1,2,3,1,2,3,...]
[1..] -- [1,1,1,...]

-- others
length [1,2,3,4] -- 4
reverse [1,2,3,4] -- [4,3,2,1]
sum [1,2,3,4] -- 10
product [1,2,3,4] -- 24
maximum [1,2,3,4] -- 4
minimum [1,2,3,4] -- 1

------------
-- TUPLES --
------------

-- 2-tuples are pairs --
fst (1,2) -- 1
snd (1,2) -- 2
zip [1,2,3] [4,5,6] -- [(1,4),(2,5),(3,6)]

------------
-- PATTERN MATCHING --
-----------
-- patterns are a way of making sure a value conforms to some form and deconstructing it
tell [] = "The list is empty"  
tell (x:[]) = "The list has one element: " ++ show x  
tell (x:y:[]) = "The list has two elements: " ++ show x ++ " and " ++ show y  
tell (x:y:_) = "This list is long. The first two elements are: " ++ show x ++ " and " ++ show y

------------
-- GUARDS --
------------
-- guards are a way of testing whether some property of a value (or several of them) are true or false
bmiTell :: (RealFloat a) => a -> String  
bmiTell bmi  
    | bmi <= 18.5 = "You're underweight, you emo, you!"  
    | bmi <= 25.0 = "You're supposedly normal. Pffft, I bet you're ugly!"  
    | bmi <= 30.0 = "You're fat! Lose some weight, fatty!"  
    | otherwise   = "You're a whale, congratulations!" -- otherwise is just True --

------------------------
-- LIST COMPREHENSION --
------------------------
-- https://wiki.haskell.org/List_comprehension

[2*x | x <- [1..10]] -- even numbers: [2,4,6,8,10,12,14,16,18,20]
[x | x <- [1..20], mod x 2 == 0] -- even numbers using boolean guard
[y | x <- [1..10], let y=2*x] -- even numbers with local let definition
[x*y | x <- [1..3], y <- [1..3]] -- two generators

-------------------
-- PRINTING SHIT --
-------------------
printStrLn
print
show

----------
-- SORT --
----------
import Data.List
sort "julie"
