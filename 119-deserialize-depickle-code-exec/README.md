When you serialize (or pickle) something in Python, it's stored as instructions that, when interpreted, reconstitute that object. There are opcodes for “create an empty list,” “append this item,” “set this attribute,” etc.

https://docs.python.org/3/library/pickle.html#what-can-be-pickled-and-unpickled

The seralized blob does NOT store the definition of the class, only the state of the instance. The class is expected to be accessible in the current import space. You can see this by printing the serialized instance, and observing that it does not change as new methods are added to the class. I think this is why, in real deserialization vulnerabilities, you need to instantiate existing classes and use them as gadgets to get what you want.

The general pickling method is simple: save the class name/type, and save the object's `.__dict__`. Upon restoring, that class has its `__new__()` method called, and its `.__dict__` updated.

To deviate from default behavior you can override:
```
object.__getnewargs_ex__()
object.__getnewargs__()
object.__getstate__()
object.__setstate__(state)
object.__reduce__()
object.__reduce_ex__(protocol)
```

Using this menu, there are probably multiple ways to execute code.

## Attempt 0

Just having a constructor be called. But:

> When a class instance is unpickled, its __init__() method is usually not invoked. The default behaviour first creates an uninitialized instance and then restores the saved attributes.

## Attempt 1

The docs say:

> Upon unpickling, if the class defines \__setstate__(), it is called with the unpickled state.

The exception is if `__reduce__()` returns no state, or state None.

So I try to override and have `__reduce__()` return non-None state, then have `__setstate()__` print something.

See `test1.py` for this.

It fails because on the remote side (the vulnerable side), class instantiation fails before `__setstate()__` can be called:

```
$ ./vulnerable.py gASVWQAAAAAAAACMB2NvcHlyZWeUjA5fcmVjb25zdHJ1Y3RvcpSTlIwIX19tYWluX1+UjAdNeUNsYXNzlJOUjAhidWlsdGluc5SMBm9iamVjdJSTlE6HlFKUjAVoZWxsb5RiLg==
Traceback (most recent call last):
  File "/Users/andrewl/repos/lwerdna/workbench/119-deserialize-depickle-code-exec/./vulnerable.py", line 13, in <module>
    pickle.loads(serialized)
AttributeError: Can't get attribute 'MyClass' on <module '__main__' from '/Users/andrewl/repos/lwerdna/workbench/119-deserialize-depickle-code-exec/./vulnerable.py'>
```

## Attempt 2

I got this method from [1].

The `__reduce__()` call can return something callable and arguments. Simply return `os.system` and arguments for reverse shell or whatever. I use `ls` to demonstrate.

```
$ ./vulnerable.py 'gASVHQAAAAAAAACMBXBvc2l4lIwGc3lzdGVtlJOUjAJsc5SFlFKULg=='
decoding gASVHQAAAAAAAACMBXBvc2l4lIwGc3lzdGVtlJOUjAJsc5SFlFKULg==
README.md	test1.py	test2.py	vulnerable.py
done
```

And the `ls` has clearly executed.

## Lesson

The first attempt didn't work because the object had to be instantiated before `__setstate__()` was called. The object cannot be instantiated because it doesn't exist on the remote (vulnerable) side.

The second attempt worked because **the `__reduce__()` function is not itself serialized**. Instead, its result becomes part of the serialized blob, and it is called **before and during** the object is instantiated. The instantiation still fails (because MyClass does not exist in the vulnerable module), but the callable is invoked by the deserializer in the attempt.

## References

1. [Exploiting Python pickles](https://davidhamann.de/2020/04/05/exploiting-python-pickle/)
2. [BlackHat 2011 - Sour Pickles, A serialised exploitation guide in one part](https://www.youtube.com/watch?v=HsZWFMKsM08)
