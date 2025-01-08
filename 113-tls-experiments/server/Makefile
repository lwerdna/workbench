.PHONY: all

all: server_key.pem server_cert.pem

server_key.pem server_cert.pem:
	openssl req -x509 -nodes -newkey rsa:4096 -keyout server_key.pem -out server_cert.pem -sha256 -days 3650 -nodes -subj "/C=XX/ST=StateName/L=CityName/O=CompanyName/OU=CompanySectionName/CN=CommonNameOrHostname"

clean:
	rm *.pem
