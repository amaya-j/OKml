
{
    open Parser
}

let digit = ['0'-'9']
let nat = digit +
let num = nat | ('-' nat)
let whitespace = (' ' | '\t' | '\n' | '\r')
let lowercase = ['a'-'z' '_']
let identchar = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']


rule tokenize = parse
    | "let" { LET }
    | "in" { IN }
    | "if" { IF }
    | "then" { THEN }
    | "else" { ELSE }
    | "rec" { REC }
    | "fun" { FUN }
    | "match" { MATCH }
    | "with" { WITH }
    | "true" { BOOL true }
    | "false" { BOOL false }
    | "()" { UNIT }
    | "::" { CONS }
    | "->" { ARROW }
    | "<>" { NEQ }
    | ">=" { GEQ }
    | "<=" { LEQ }
    | "&&" { AND }
    | "||" { OR }
    | "=" { EQ }
    | "+" { PLUS }
    | '-' digit+ as n { INT (int_of_string n) } 
    | "-" { MINUS }
    | "*" { TIMES }
    | "/" { DIV }
    | "<" { LT }
    | ">" { GT }
    | "(" { LPAREN }
    | ")" { RPAREN }
    | "[" { LBRACKET }
    | "]" { RBRACKET }
    | "," { COMMA }
    | "|" { BAR }
    | lowercase identchar* as id { IDENT id }
    | num { INT (lexbuf |> Lexing.lexeme |> int_of_string) }
    | whitespace { tokenize lexbuf } 
    | eof { EOF }
    | _ as c { failwith ("unexpected character: " ^ (Char.escaped c)) }
