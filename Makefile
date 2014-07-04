all: ToyLisp.c
	gcc -s -Wall -static -O3 -o ToyLisp ToyLisp.c
run: ToyLisp
	./ToyLisp
clean:
	rm -f ToyLisp
