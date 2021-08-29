TESTS = $(wildcard *.saml)
SAML = dune exec ../src/saml.exe

all: test

test: $(TESTS)
	@for i in $(TESTS); do \
	  echo "Testing $$i..."; \
	  $(SAML) $$i; \
	done
