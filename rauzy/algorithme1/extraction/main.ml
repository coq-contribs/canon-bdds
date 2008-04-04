open Unix;;

let string_of_bool b = 
  if b then  "Tautology"
       else  "Not a tautology";; 



let analyze_file channel  =
try
  let lexbuf = Lexing.from_channel channel in
    Hashtbl.clear Lexer.h;
    Lexer.nb_var := 0;
    Parser.main Lexer.token lexbuf
with
      _ -> failwith "syntax error"
;;


let main () =
  let channel = (in_channel_of_descr  ( openfile Sys.argv.(1) [O_RDONLY] 0644 ))
  in
  let e = analyze_file channel
  in 
  print_string (string_of_bool (Suresnes.One=Suresnes.existence e));
  print_newline();
  exit 0;;

main ();;
