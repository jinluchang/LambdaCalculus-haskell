all : interpreter encode decode

interpreter :
	ghc -Wall -O2 -o interpreter --make Interpreter.hs

encode :
	ghc -Wall -O2 -o encode --make Encode.hs

decode :
	ghc -Wall -O2 -o decode --make Decode.hs

prof :
	ghc -prof -auto-all -Wall -O2 -o interpreter --make Interpreter.hs

clean :
	rm interpreter encode decode *.o *.hi || :
