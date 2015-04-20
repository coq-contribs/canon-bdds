CC= $(CAMLBIN)ocamlopt
FLAGS = -cclib -lunix
LIB= unix.cmxa

LEX= $(CAMLBIN)ocamllex
YACC= $(CAMLBIN)ocamlyacc

OBJ_I = suresnes.cmi \
	parser.cmi

OBJ= 	suresnes.cmx \
	lexer.cmx \
	parser.cmx \
	main.cmx \

PROG= suresnes


all : 	$(PROG)

$(PROG) : $(OBJ_I) $(OBJ)
	$(CC) $(FLAGS) -o $(PROG) $(LIB) $(OBJ)

parser.ml : parser.mly
	$(YACC) parser.mly

parser.mli : parser.ml

lexer.ml : lexer.mll
	$(LEX) lexer.mll

%.cmi : %.mli
	$(CC) -c $<

%.cmx : %.ml
	$(CC) -c $<

%.ml.d : %.ml | lexer.ml
	$(CAMLBIN)ocamldep $< > $@

clean :
	rm -f *.o *.ml.d *.cmx *.cmi \
	$(PROG) \
	suresnes.ml \
	lexer.ml \
	parser.ml \
	parser.mli

ifneq ($(MAKECMDGOALS),clean)
include $(OBJ:.cmx=.ml.d)
endif
