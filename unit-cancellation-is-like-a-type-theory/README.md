Unit cancellation (also called dimensional analysis or unit analysis) is kind of like a simple type theory.

Imagine if quantities were endowed by a type consisting of a nonempty multiset set of strings on "top" and a possibly empty multiset of strings on "bottom".

For example, quantity 128.0 and "top" strings {"ounce"} and bottom strings {"gallon"}. We might write it as:

$$
128\frac{\{ounce\}}{\{gallon\}}
$$

Or 3.7 with top {"mile"} and bottom {} would be written as:
$$
2.5\frac{\{mile\}}{\{\}}
$$
We have some simple type checking rules:

* multiplication admits operands of any type
* addition requires the operands be the same type

And we we have some simple type inference rules:

* the type of a product has "top" and "bottom" sets the respective unions of the multiplicands
* the type of a sum is the type of its addends

For example:
$$
2.5\frac{\{mile\}}{\{\}} \times 5280\frac{\{feet\}}{\{mile\}} = 13200\frac{\{mile, feet\}}{\{mile\}}
$$
For every pair of strings that appears both in the top and bottom set, they can be permanently removed, so the above result becomes:
$$
13200\frac{\{feet\}}{\{\}}
$$
See [./demo.py](./demo.py) for this implemented by utilizing object oriented programming in Python and computing some examples:

```python
    # Example: convert 2.5 miles to inches
    result =    Quantity(2.5, ['mile'], []) * \
                Quantity(5280, ['foot'], ['mile']) * \
                Quantity(12, ['inch'], ['foot'])
```

And the result is `158400.0 {inch}`.

```python
    # Example: convert 65 miles per hour to feet per second
    result =    Quantity(65, ['mile'], ['hour']) * \
                Quantity(5280, ['foot'], ['mile']) * \
                Quantity(1/60, ['hour'], ['minute']) * \
                Quantity(1/60, ['minute'], ['second'])
```

And the result is `95.33333333333333 {foot}/{second}`.

```python
    # Example: convert 1km^2 to m^2
    assert str(Quantity(2.5, ['kilometer', 'kilometer'], [])) == '2.5 {kilometer^2}'

    result =    Quantity(1, ['kilometer', 'kilometer'], []) * \
                Quantity(1000, ['meter'], ['kilometer']) * \
                Quantity(1000, ['meter'], ['kilometer'])
```

And the result is `1000000 {meter^2}`.
