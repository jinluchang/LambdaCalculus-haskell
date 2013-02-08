all :
	ghc -Wall -O2 -o calc --make Main.hs

clean :
	rm calc *.o *.hi
