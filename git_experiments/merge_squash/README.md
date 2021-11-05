Given this schema:

![](./1.png)

### method1: merge

```
git checkout master
git merge --squash feature
git commit -m "squashed feature"
```

puts a new commit at master, and does NOT merge the two branches. Feature branch can now be abandoned:

![](./2.png)



