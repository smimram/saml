TESTS = $(wildcard *.saml)
SAML = dune exec ../src/saml.exe

all: test

test:
	@for i in $(TESTS); do \
	  echo "Testing $$i..."; \
	  $(SAML) $$i || exit 1; \
	done

.PHONY: test
