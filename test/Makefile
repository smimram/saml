TESTS = $(addprefix passed/,$(wildcard *.saml))
SAML = dune exec ../src/saml.exe

all: test

test: $(TESTS)

passed/%: %
	@mkdir -p passed
	@echo "## Testing $<"
	@echo
	@$(SAML) $< && touch $@

clean:
	rm -rf passed
