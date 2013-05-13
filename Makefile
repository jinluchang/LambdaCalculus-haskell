all : compiler interpreter encode decode rename

compiler : *.hs
	ghc -Wall -O2 -o compiler --make Compiler.hs

interpreter : *.hs
	ghc -Wall -O2 -o interpreter --make Interpreter.hs

encode : *.hs
	ghc -Wall -O2 -o encode --make Encode.hs

decode : *.hs
	ghc -Wall -O2 -o decode --make Decode.hs

rename : *.hs
	ghc -Wall -O2 -o rename --make Rename.hs

prof : *.hs
	ghc -prof -auto-all -Wall -O2 -o interpreter --make Interpreter.hs

TEST=input/queens

test-compile : compiler
	rm -rf test || :
	mkdir test
	./compiler -O < $(TEST) > test/test.hs
	cd test && ghc --make test.hs && time ./test

test-compile-c : compiler
	rm -rf test || :
	mkdir test
	cp lam_stg.h test
	./compiler -O -C < $(TEST) > test/test.c
	cd test && gcc -DNDEBUG -O3 test.c && time ./a.out

clean :
	rm compiler interpreter encode decode rename *.o *.hi || :
