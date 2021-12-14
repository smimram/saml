all install clean:
	make -C src $@

test:
	make -C test

.PHONY: test
