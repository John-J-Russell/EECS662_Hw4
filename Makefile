RM = rm

hw2p1t: Sugar.hs Core.hs Main.hs
	ghc -o hw2 --make Main.hs

clean:
	$(RM) *.o *.hi hw2*
