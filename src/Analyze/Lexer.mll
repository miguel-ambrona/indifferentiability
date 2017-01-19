{
  open Parser

  exception Error of string

  let unterminated_comment () = raise (Error "unterminated comment")
  let unterminated_string  () = raise (Error "unterminated string")
}

let blank = [' ' '\t' '\r' '\n']
let newline = '\n'
let letters = ['a'-'z' 'A'-'Z']
let alphanum = ['a'-'z' 'A'-'Z' '0'-'9' '~']

rule lex = parse
  | blank+  { lex lexbuf }
  | "(*"    { comment lexbuf; lex lexbuf }
  | newline { Lexing.new_line lexbuf; lex lexbuf }
  | eof     { EOF }
  | "."     { DOT }
  | "("     { LPAR }
  | ")"     { RPAR }
  | "="     { EQ }
  | "<>"    { INEQ }
  | "+"     { PLUS }
  | ","     { COMMA }
  | ":"     { COLON }
  | ";"     { SEMICOLON }
  | "^"     { CARET }

  | ":="       { DEFINE }
  | "{0,1}"    { ZO }
  | "<-$"      { SAMP }
  | "->"       { TO }
  | "rounds"   { ROUNDS }
  | "oracle"   { ORACLE }
  | "x"        { TIMES }
  | "check"    { CHECK }
  | "return"   { RETURN }
  | "attacker" { ATTACKER }
  | "0"        { ZERO }
 
  | letters alphanum* as s       { NAME s}


and comment = parse
  | "*)"        { () }
  | "(*"        { comment lexbuf; comment lexbuf }
  | newline     { Lexing.new_line lexbuf; comment lexbuf }
  | eof         { unterminated_comment () }
  | _           { comment lexbuf }
