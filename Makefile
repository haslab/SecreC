parser:
	alex src/Language/SecreC/Parser/Lexer.x
	happy -i src/Language/SecreC/Parser/Parser.y
run:
	ghc --make Test.hs -isrc
	./test
main:
	ghc --make Main.hs -isrc -o secrec
	./secrec