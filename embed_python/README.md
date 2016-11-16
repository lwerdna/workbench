# experiments in embedding python

* call3.c invokes the go() methods in a.py, b.py, c.py
* capture_stdout.c invokes the go() methods but saves all python stdout to a string
* full_embed.c links against a self contained python.a, not relying on a system wide python install
