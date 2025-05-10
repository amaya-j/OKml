{
  open Parser
}


let digit      = ['0'-'9']
let nat        = digit+
let whitespace = [' ' '\t' '\r' '\n']
let lowercase  = ['a'-'z''_']
let identchar  = ['a'-'z''A'-'Z''0'-'9''_''\'']

rule tokenize = parse
  | "let"     { LET }
  | "in"      { IN }
  | "if"      { IF }
  | "then"    { THEN }
  | "else"    { ELSE }
  | "rec"     { REC }
  | "fun"     { FUN }
  | "match"   { MATCH }
  | "with"    { WITH }


  | "true"    { BOOL true }
  | "false"   { BOOL false }
  | "not"     { NOT }
  | "()"      { UNIT }
  | "::"      { CONS }
  | "->"      { ARROW }
  | "<>"      { NEQ }
  | ">="      { GEQ }
  | "<="      { LEQ }
  | "&&"      { AND }
  | "||"      { OR }
  | "="       { EQ }
  | "+"       { PLUS }
  | "-"       { MINUS }    (* always lex a lone “-” as MINUS *)
  | "*"       { TIMES }
  | "/"       { DIV }
  | "<"       { LT }
  | ">"       { GT }
  | "("       { LPAREN }
  | ")"       { RPAREN }
  | "["       { LBRACKET }
  | "]"       { RBRACKET }
  | ","       { COMMA }
  | "|"       { BAR }


  | lowercase identchar* as id
              { IDENT id }

  | nat as n  { INT (int_of_string n) }

  | whitespace { tokenize lexbuf }

  | eof       { EOF }

  | _ as c    { 
      failwith ("unexpected character in lexer: " ^ Char.escaped c)
    }