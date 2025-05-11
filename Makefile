CFLAGS=-std=c11 -g -fno-common
CODE=""

chibicc: *.go
	rm -f tmp* && go build -o chibicc .

test: chibicc
	./test.sh
	./test-driver.sh

clean:
	rm -f chibicc *.o *~ tmp*

exec: chibicc
	./chibicc "${CODE}"

.PHONY: test clean
