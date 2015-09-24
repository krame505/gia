grammar gia:concretesyntax;

temp_imp_ide_font font_all color(123, 0, 82) bold;
temp_imp_ide_font font_comments color(63, 95, 191) italic;
temp_imp_ide_font font_special_symbol color(71, 71, 141);
--temp_imp_ide_font font_equal color(63, 127, 95);


lexer class Comment font = font_comments;
lexer class Keyword font = font_all;
--lexer class Assignment font=font_equal;
lexer class Symbol font = font_special_symbol;

ignore terminal LineComment_t  /#.*/ lexer classes {Comment};
ignore terminal BlockComment_t /#\-([^#]|[\r\n]|([#]+([^#\-]|[\r\n])))*[\-]+[#]/ lexer classes {Comment};

ignore terminal Spaces_t  /[\t\ ]+/ lexer classes {Comment};
ignore terminal Newline_t /\n/ lexer classes {Comment};

lexer class Identifier submits to Keyword;

terminal Id_t /[A-Za-z][A-Za-z_0-9]*/ lexer classes {Identifier};

-- Literals
lexer class Literal;

terminal IntConstant_t    /[\-]?[0-9]+/ lexer classes {Literal};
terminal StringConstant_t /[\"]([^\"]|[\\][\"])*[\"]/ lexer classes {Literal};

-- Keywords
terminal Wildcard_t '_'     lexer classes {Keyword};
terminal None_t    'none'   lexer classes {Keyword};
terminal Return_t  'return' lexer classes {Keyword};
terminal Use_t     'use'    lexer classes {Keyword};
terminal Lambda_t  'fn'     lexer classes {Keyword};
terminal If_t      'if'     lexer classes {Keyword};
terminal Then_t    'then'   lexer classes {Keyword};
terminal Else_t    'else'   lexer classes {Keyword}, precedence = 0, association = left;

-- Structural symbols
terminal Comma_t      ',';
terminal Semi_t       ';';
terminal LParen_t     '(';
terminal LALParen_t   /\(/ association = left; -- Function calls
terminal RParen_t     ')'  precedence = 1, association = left; -- evidently, part of dangling-else?
terminal LALBracket_t /\[/ association = left;
terminal LBracket_t   '[';
terminal RBracket_t   ']';
terminal LCurly_t     '{';
terminal RCurly_t     '}';
terminal Colon_t      ':';
terminal Assign_t     '='  lexer classes {Symbol};

-- Operators
terminal Match_t    '~'  precedence = 0, association = left, lexer classes {Symbol};
terminal Cons_t     '::' precedence = 1, association = right, lexer classes {Symbol};
terminal Or_t       '|'  precedence = 2, association = left, lexer classes {Symbol};
terminal Xor_t      '^'  precedence = 3, association = left, lexer classes {Symbol};
terminal And_t      '&'  precedence = 4, association = left, lexer classes {Symbol};
terminal Eq_t       '==' precedence = 5, association = left, lexer classes {Symbol};
terminal Neq_t      '!=' precedence = 5, association = left, lexer classes {Symbol};
terminal Lt_t       '<'  precedence = 6, association = left, lexer classes {Symbol};
terminal Gt_t       '>'  precedence = 6, association = left, lexer classes {Symbol};
terminal Lte_t      '<=' precedence = 6, association = left, lexer classes {Symbol};
terminal Gte_t      '>=' precedence = 6, association = left, lexer classes {Symbol};
terminal Minus_t    '-'  precedence = 7, association = left, lexer classes {Symbol}; -- negative
terminal Plus_t     '+'  precedence = 7, association = left,  lexer classes {Symbol}; -- positive
terminal Star_t     '*'  precedence = 8, association = left, lexer classes {Symbol}; -- pointer, deref
terminal Divide_t   '/'  precedence = 8, association = left, lexer classes {Symbol};
terminal Mod_t      '%'  precedence = 8, association = left, lexer classes {Symbol};
terminal Capture_t  '@'  precedence = 9, lexer classes {Symbol};
terminal Dot_t      '.'  precedence = 9;