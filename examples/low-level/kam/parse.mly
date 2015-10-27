%{
  open Syntax
%} 

%token <string> IDENT 
%token <int> INT
%token VAR NAME APP ABS BINDER LPAREN RPAREN
                    
/* These are artificial */
%token WHITESPADE EOF

%start file
%type <tm list> file

%%
file: 
  | terms EOF
      { $1 }

terms:
  |   { [] }
  | term terms { $1::$2 }

term: 
  | LPAREN VAR INT RPAREN { Var ($3) }
  | LPAREN NAME IDENT RPAREN { Name ($3) }
  | LPAREN APP term term RPAREN { App($3, $4) }
  | LPAREN ABS term term RPAREN { Abs($3, $4) }
  | LPAREN BINDER term term RPAREN { Binder($3, $4) }
           
