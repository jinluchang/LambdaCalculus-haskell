all : interpreter encode decode rename

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

clean :
	rm interpreter encode decode rename *.o *.hi || :
