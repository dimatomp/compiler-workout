SHELL := /bin/bash
#SHELL := /run/current-system/sw/bin/bash

.PHONY: all regression

all:
	pushd src && make && popd

install: ;

regression:
	pushd regression && ./test.sh && popd

clean:
	pushd src && make clean && popd

