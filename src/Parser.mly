%{
  open Attacker           
%}

%token EOF
%token DOT
%token LPAR
%token RPAR
%token EQ
%token INEQ
%token PLUS
%token COMMA
%token COLON
%token SEMICOLON
%token CARET
       
%token DEFINE
%token ZO
%token SAMP
%token TO
%token ROUNDS
%token ORACLE
%token TIMES
%token CHECK
%token RETURN
%token ATTACKER
%token ZERO

%token <string> NAME


/************************************************************************/
/* Production types */

%type <Eval.cmd list> cmds_t

/************************************************************************/
/* Start productions */

%start cmds_t

%%

/************************************************************************/
/* Types */

var :
| s = NAME    { s }
      
set :
| v = NAME; DEFINE; ZO; CARET; n = NAME;      { Eval.DefineSet(v, Eval.ZO(n)) }
                                       
rounds :
| ROUNDS; names = separated_list(COMMA, var); COLON; s1 = NAME; TO; s2 = NAME;
  { Eval.DefineRounds (names, s1, s2) }
    
oracle :
| ORACLE; s = NAME; COLON; input = separated_list(TIMES, var); TO; output = separated_list(TIMES, var); ;
  { Eval.DefineOracle (s, input, output) }

is_eq :
| EQ EQ;  { Eq }
| INEQ;   { Ineq }

var_or_zero :
| v = NAME; { v }
| ZERO;     { "0" }
  
command :
| v = NAME; SAMP; s = NAME    { Eval.Pseudo_sample(v,s) }
| v = NAME; EQ; f = NAME; LPAR; inputs = separated_list(COMMA, var); RPAR;  { Eval.Pseudo_fun(f, inputs, [v]) }
| LPAR; outputs = separated_list(COMMA, var); RPAR; EQ; f = NAME; LPAR; inputs = separated_list(COMMA, var); RPAR;
  { Eval.Pseudo_fun(f, inputs, outputs) }
| v = NAME; EQ; list = separated_list(PLUS, var); { Eval.Pseudo_xor(v, list) }
| CHECK; v1 = var_or_zero; eq = is_eq; v2 = var_or_zero;  { Eval.Pseudo_check(v1,eq,v2) }
| RETURN; list = separated_list(COMMA, var);  { Eval.Pseudo_return(list) }
  
oracle_code :
| s = NAME; LPAR; input = separated_list(COMMA, var); RPAR; DEFINE; commands = separated_list(SEMICOLON, command);
  { Eval.OracleCode (s, input, commands) }

attacker :
| ATTACKER; DEFINE; commands = separated_list(SEMICOLON, command);  { Eval.Attacker(commands) }
    

cmd :
| s = set; DOT;          { s } 
| r = rounds; DOT;       { r }
| o = oracle; DOT;       { o }
| o = oracle_code; DOT;  { o }
| a = attacker; DOT;     { a }
                   
cmds_t : cs = list(cmd); EOF; { cs };
