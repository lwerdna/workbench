Simple HTTP post of a file.

post.c sends a file to the HTTP server, is processed by some CGI

# server options
* set up a real server like apache or nginx
* use python (place script.py in ./cgi/):
```python
#!/usr/bin/python
import CGIHTTPServer
import BaseHTTPServer
class Handler(CGIHTTPServer.CGIHTTPRequestHandler):
    cgi_directories = ["/cgi"]
PORT = 8080
httpd = BaseHTTPServer.HTTPServer(("", PORT), Handler)
print "serving at port", PORT
httpd.serve_forever()
```
* use thttpd `thttpd -p 8080 -c "*.py" -D

# CGI options
To upload the file, the client requests a script, while sending it a parameter of the file name and file data. The script can be written in any language, but a python one is provided because the libraries built into typical python installs make it so simple without having to manually parse environment QUERY_STRING, etc. See script.py.
