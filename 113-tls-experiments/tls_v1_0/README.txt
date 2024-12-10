Generate private key "key.pem" and certificate "cert.pem":
  openssl req -x509 -nodes -newkey rsa:4096 -keyout key.pem -out cert.pem -sha256 -days 3650 -nodes -subj "/C=XX/ST=StateName/L=CityName/O=CompanyName/OU=CompanySectionName/CN=CommonNameOrHostname"

On one terminal:
  ./server_cert.py

On another:
  ./client_cert.py localhost 31337
