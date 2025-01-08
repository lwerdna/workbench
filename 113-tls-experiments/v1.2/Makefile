.PHONY: all

all: client_key.pem client_cert.pem

client_key.pem client_cert.pem:
	openssl req -x509 -nodes -newkey rsa:4096 -keyout client_key.pem -out client_cert.pem -sha256 -days 3650 -nodes -subj "/C=XX/ST=StateName/L=CityName/O=CompanyName/OU=CompanySectionName/CN=CommonNameOrHostname"

clean:
	rm *.pem
