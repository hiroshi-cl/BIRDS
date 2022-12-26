 {
    open Parser;;        (* The type token is defined in parser.mli *)
    open Utils ;;
    let keyword_table = Hashtbl.create 100
    let _ =
        List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
        ["AND", AND;
        "And", AND;
        "and", AND;
        "OR", OR;
        "Or", OR;
        "or", OR;
        "NOT", NOT;
        "Not", NOT;
        "not", NOT;
        "FALSE", FF;
        "False", FF;
        "false", FF;
        "BOT", BOT;
        "Bot", BOT;
        "bot", BOT;
        "TRUE", TT;
        "True", TT;
        "true", TT;
        "TOP", TOP;
        "Top", TOP;
        "top", TOP;
        "null", NULL;
        "Null", NULL;
        "NULL", NULL;
        "int", SINT;
        "INT", SINT;
        "real", SREAL;
        "REAL", SREAL;
        "string", SSTRING;
        "STRING", SSTRING;
        "bool", SBOOL;
        "BOOL", SBOOL;
        "source", SMARK;
        "Source", SMARK;
        "SOURCE", SMARK;
        "view", VMARK;
        "View", VMARK;
        "VIEW", VMARK;
        "pk", PK;
        "Pk", PK;
        "PK", PK;
        "pK", PK;
        "primarykey", PK;
<<<<<<< HEAD
=======
        "SELECT", SELECT;
        "select", SELECT;
        "FROM", FROM;
        "from", FROM;
        "WHERE", WHERE;
        "where", WHERE;
        "INSERT", INSERT;
        "insert", INSERT;
        "DELETE", DELETE;
        "delete", DELETE;
        "UPDATE", UPDATE;
        "update", UPDATE;
        "SET", SET;
        "set", SET;
        "INTO", INTO;
        "into", INTO;
        "VALUES", VALUES;
        "values", VALUES;
        "EXISTS", EXISTS;
        "exists", EXISTS;
>>>>>>> d96beeb (introduce files)
        ]
(*		exception Eof
*)
 }

  rule token = parse
      [' ' '\t']     				{ token lexbuf }    (* skip blanks *)
    | ['\n' ]        				{ Lexing.new_line lexbuf; token lexbuf }    (* skip newline *)
    | '%''\n'        			{ Lexing.new_line lexbuf; token lexbuf }    (* skip comments *)
    | '%'[^'\n''v''s'][^'\n']*'\n'        			{ Lexing.new_line lexbuf; token lexbuf }    (* skip comments *)
    | '%'[^'\n''v''s'][^'\n']*eof        			{ Lexing.new_line lexbuf; token lexbuf }    (* skip comments *)
    | '%'['v''s'][^':'][^'\n']*'\n'        			{ Lexing.new_line lexbuf; token lexbuf }    (* skip comments *)
    | '%'['v''s'][^':'][^'\n']*eof        			{ Lexing.new_line lexbuf; token lexbuf }    (* skip comments *)
    | ['0'-'9']+ as lxm 			{ INT (int_of_string lxm) }
    | ['0'-'9']*'.'?['0'-'9']+(['e''E']['-''+']?['0'-'9']+)?  as lxm  { FLOAT (float_of_string (lxm)) }
    | '\''(('\'''\'')|[^'\n''\''])*'\'' as lxm  { STRING(lxm) }
<<<<<<< HEAD
    | '_'*['a'-'z']['a'-'z''0'-'9''_']* as lxm 	{ 
=======
    | '_'*['a'-'z''*']['a'-'z''0'-'9''_']* as lxm 	{ 
>>>>>>> d96beeb (introduce files)
        try
            Hashtbl.find keyword_table lxm
        with Not_found -> RELNAME(lxm) }
    | '_'*['A'-'Z']['A'-'Z''0'-'9''_']*'\''* as lxm 	{
        try
            Hashtbl.find keyword_table lxm
        with Not_found -> VARNAME(lxm)
						}
    | "_|_"                                       { BOT }
    | "%v:"            				{ VMARK }  (* view mark *)
    | "%s:"                         { SMARK } (* source relation mark *)
    | ":-"          				{ IMPLIEDBY }  
    | "<-"          				{ IMPLIEDBY }  
    | "?-"            				{ QMARK }  (* query mark *)
    | "?_"                                       { ANONVAR }
    | "<>"            				{ NE }
    | "\\="            				{ NE }
    | "<="                                      { LE }
    | ">="                                      { GE }
    | "^"                                       { CONCAT }
    | "←"           				{ IMPLIEDBY } 
    | "¬"           				{ NOT }  
    | "!"           				{ NOT }  
    | '.'            				{ DOT }    (* end of rule or query *)
    | ','            				{ SEP }
    | '('            				{ LPAREN }
    | ')'            				{ RPAREN }
    | '['            				{ LBRACKET }
    | ']'            				{ RBRACKET }
    | '='            				{ EQ }
    | '_'                                       { ANONVAR }
    | ':'          				{ TYPING }
    | "⊥"                                       { BOT }
    | "⊤"                                       { TOP } 
    | '<'                                       { LT }
    | '>'                                       { GT }
    | '+'                                       { PLUS }
    | '-'                                       { MINUS }
    | '*'                                       { TIMES }
    | '/'                                       { DIVIDE }   
	| eof            { EOF }
    | _                      { spec_lex_error lexbuf }
	
