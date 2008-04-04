%{
open Suresnes

let rec i2n = function 0 -> O | n -> (S (i2n (pred n)));;

let rec n2i = function O -> 0 | (S n) -> succ (n2i n);;

%}

%token <int> VAR
%token AND OR NOT EQ IMPL TRUE FALSE
%token LPAREN RPAREN
%token EOF

%right EQ IMPL
%left OR
%left AND  
%nonassoc NOT 


%start main      
%type <Suresnes.bool_exp> main

%%

main:
    expression EOF              {  $1 }
;
expression :
    VAR                  	{ Var (i2n $1) }
  | TRUE 		  	{ Tr }
  | FALSE		    	{ Fa }
  | LPAREN expression RPAREN    { $2 }
  | expression AND expression 	{ ANd ($1,$3) }
  | expression OR expression    { Or ($1,$3) }
  | expression IMPL expression  { Or (Not $1,$3) }
  | expression EQ expression	{ ANd(Or (Not $1,$3),Or (Not $3,$1)) }
  | NOT expression              { (Not $2) }
;


