CFLAGS=-std=c11 -g -fno-common

chibicc: *.go
	rm -f tmp* && go build -o chibicc .

test: chibicc
	./test.sh

clean:
	rm -f chibicc *.o *~ tmp*

.PHONY: test clean
