# Step 1.

Here's the incoming dataset:

```
feature0    feature1 feature2 feature3 classification
young       myope    no       reduced  no lenses
young       myope    no       normal   soft
young       myope    yes      reduced  no lenses
young       myope    yes      normal   hard
young       hyper    no       reduced  no lenses
young       hyper    no       normal   soft
young       hyper    yes      reduced  no lenses
young       hyper    yes      normal   hard
pre         myope    no       reduced  no lenses
pre         myope    no       normal   soft
pre         myope    yes      reduced  no lenses
pre         myope    yes      normal   hard
pre         hyper    no       reduced  no lenses
pre         hyper    no       normal   soft
pre         hyper    yes      reduced  no lenses
pre         hyper    yes      normal   no lenses
presbyopic  myope    no       reduced  no lenses
presbyopic  myope    no       normal   no lenses
presbyopic  myope    yes      reduced  no lenses
presbyopic  myope    yes      normal   hard
presbyopic  hyper    no       reduced  no lenses
presbyopic  hyper    no       normal   soft
presbyopic  hyper    yes      reduced  no lenses
presbyopic  hyper    yes      normal   no lenses
```

The outcomes are 15x "no lenses", 5x "soft", 4x "hard" which has entropy/unpredictability:

```
pr0=15/(15+5+4)
pr1=5/(15+5+4)
pr2=4/(15+5+4)
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.3260875253642983
```

## Step 1 candidate: Split on feature0

feature0 == "young" results in 8 rows of the original 24:

```
feature1 feature2 feature3 classification
myope    no       reduced  no lenses
myope    no       normal   soft
myope    yes      reduced  no lenses
myope    yes      normal   hard
hyper    no       reduced  no lenses
hyper    no       normal   soft
hyper    yes      reduced  no lenses
hyper    yes      normal   hard
```

The outcomes are 4x "no lenses", 2x "soft", 2x "hard", which has entropy/unpredictability:

```
pr0=4/(4+2+2)
pr1=2/(4+2+2)
pr2=2/(4+2+2)
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.5
```

feature0 == "pre" results in 8 rows of the original 24:

```
feature1 feature2 feature3 classification
myope    no       reduced  no lenses
myope    no       normal   soft
myope    yes      reduced  no lenses
myope    yes      normal   hard
hyper    no       reduced  no lenses
hyper    no       normal   soft
hyper    yes      reduced  no lenses
hyper    yes      normal   no lenses
```

The outcomes are 5x "no lenses", 2x "soft", 1x "hard", which has entropy/unpredictability:

```
pr0=5/(5+2+1)
pr1=2/(5+2+1)
pr2=1/(5+2+1)
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.2987949406953987
```

feature0 == "presbyopic" results in 8 rows of the original 24

```
feature1 feature2 feature3 classification
myope    no       reduced  no lenses
myope    no       normal   no lenses
myope    yes      reduced  no lenses
myope    yes      normal   hard
hyper    no       reduced  no lenses
hyper    no       normal   soft
hyper    yes      reduced  no lenses
hyper    yes      normal   no lenses
```

The outcomes are 6x lenses", 1x "soft", 1x "hard", which has entropy/unpredictability:

```
pr0=6/(6+1+1)
pr1=1/(6+1+1)
pr2=1/(6+1+1)
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.0612781244591327
```

Total information gain from splitting on feature0 is thus:

```
1.3260875253642983 - ((8/24)*1.5 + (8/24)*1.2987949406953987 + (8/24)*1.0612781244591327) = 0.03939650364612124
```

## Step 1 candidate: Split on feature1

feature1 == "myope" results in 12 rows of the original 24:

```
feature0    feature2 feature3 classification
young       no       reduced  no lenses
young       no       normal   soft
young       yes      reduced  no lenses
young       yes      normal   hard
pre         no       reduced  no lenses
pre         no       normal   soft
pre         yes      reduced  no lenses
pre         yes      normal   hard
presbyopic  no       reduced  no lenses
presbyopic  no       normal   no lenses
presbyopic  yes      reduced  no lenses
presbyopic  yes      normal   hard
```

The outcomes are 7x "no lenses", 2x "soft", 3x "hard", which has entropy/unpredictability:

```
pr0, pr1, pr2 = 7/12, 2/12, 3/12
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.384431504340598
```

feature1 == "hyper" results in 12 rows of the original 24:

```
feature0    feature2 feature3 classification
young       no       reduced  no lenses
young       no       normal   soft
young       yes      reduced  no lenses
young       yes      normal   hard
pre         no       reduced  no lenses
pre         no       normal   soft
pre         yes      reduced  no lenses
pre         yes      normal   no lenses
presbyopic  no       reduced  no lenses
presbyopic  no       normal   soft
presbyopic  yes      reduced  no lenses
presbyopic  yes      normal   no lenses
```

The outcomes are 8x "no lenses", 3x "soft", 1x "hard", which has entropy/unpredictability:

```
pr0, pr1, pr2 = 8/12, 3/12, 1/12
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.188721875540867
```

Total information gain from splitting on feature1 is thus:

```
1.3260875253642983 - ((12/24)*1.384431504340598 + (12/24)*1.188721875540867) = 0.039510835423565815
```

## Step 1 candidate: Split on feature2

feature2 == "no" results in 12 rows of the original 24:

```
feature0    feature1 feature3 classification
young       myope    reduced  no lenses
young       myope    normal   soft
young       hyper    reduced  no lenses
young       hyper    normal   soft
pre         myope    reduced  no lenses
pre         myope    normal   soft
pre         hyper    reduced  no lenses
pre         hyper    normal   soft
presbyopic  myope    reduced  no lenses
presbyopic  myope    normal   no lenses
presbyopic  hyper    reduced  no lenses
presbyopic  hyper    normal   soft
```

The outcomes are 7x "no lenses", 5x "soft", which has entropy/predictability:

```
pr0, pr1 = 7/12, 5/12
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2)
0.9798687566511527
```

feature2 == "yes" results in 12 rows of the original 24:

```
feature0    feature1 feature3 classification
young       myope    reduced  no lenses
young       myope    normal   hard
young       hyper    reduced  no lenses
young       hyper    normal   hard
pre         myope    reduced  no lenses
pre         myope    normal   hard
pre         hyper    reduced  no lenses
pre         hyper    normal   no lenses
presbyopic  myope    reduced  no lenses
presbyopic  myope    normal   hard
presbyopic  hyper    reduced  no lenses
presbyopic  hyper    normal   no lenses
```

The outcomes are 8x "no lenses", 4x "hard", which has entropy/unpredictability:

```
pr0, pr1 = 8/12, 4/12
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2)
0.9182958340544896
```

Total information gain from splitting on feature2 is thus:

```
1.3260875253642983 - ((12/24)*0.9798687566511527 + (12/24)*0.9182958340544896) = 0.37700523001147723
```

## Step 1 candidate: Split on feature3 

feature3 == "normal" results in 12 rows of the original 24:

```
feature0    feature1 feature2 classification
young       myope    no       soft
young       myope    yes      hard
young       hyper    no       soft
young       hyper    yes      hard
pre         myope    no       soft
pre         myope    yes      hard
pre         hyper    no       soft
pre         hyper    yes      no lenses
presbyopic  myope    no       no lenses
presbyopic  myope    yes      hard
presbyopic  hyper    no       soft
presbyopic  hyper    yes      no lenses
```

The outcomes are 3x "no lenses", 5x "soft", 4x "hard", which has entropy/unpredictability:

```
pr0, pr1, pr2 = 3/12, 5/12, 4/12
pr0*math.log(1/pr0,2) + pr1*math.log(1/pr1,2) + pr2*math.log(1/pr2,2)
1.5545851693377997
```

feature3 == "reduced" results in 12 rows of the original 24:

```
feature0    feature1 feature2 classification
young       myope    no       no lenses
young       myope    yes      no lenses
young       hyper    no       no lenses
young       hyper    yes      no lenses
pre         myope    no       no lenses
pre         myope    yes      no lenses
pre         hyper    no       no lenses
pre         hyper    yes      no lenses
presbyopic  myope    no       no lenses
presbyopic  myope    yes      no lenses
presbyopic  hyper    no       no lenses
presbyopic  hyper    yes      no lenses
```

The outcomes are 12x "no lenses", 0x "soft", 0x "hard", which has is completely predictable:

```
pr0, pr1, pr2 = 12/12, 0/12, 0/12
pr0*math.log(1/pr0,2)
0.0
```

Total information gain from splitting on feature3 is thus:

```
1.3260875253642983 - ((12/24)*1.5545851693377997 + (12/24)*0) = 0.5487949406953985
```

In summary,
splitting on feature0 gains 0.0393965036461212 bits
splitting on feature1 gains 0.0395108354235658 bits
splitting on feature2 gains 0.3770052300114772 bits
splitting on feature3 gains 0.5487949406953985 bits

And thus we should split on feature3.
