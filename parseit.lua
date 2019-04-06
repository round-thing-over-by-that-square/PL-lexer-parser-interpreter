-- parseit.lua
-- Alex Lewandowski
-- 3/1/19 - 3/8/19
-- Recursive-Descent Parser for Jerboa PL
-- Requires lexit.lua
--
-- based, in part, on rdparser4.lua and assigment
-- notes, both written by Glenn G. Chappell 
--
-- Grammar
-- Start symbol: program
--  (1)    	program	  →  	stmt_list
--  (2)    	stmt_list	  →  	{ statement }
--  (3)    	statement	  →  	‘write’ ‘(’ write_arg { ‘,’ write_arg } ‘)’
--  (4)    	 	|  	‘def’ ID ‘(’ ‘)’ stmt_list ‘end’
--  (5)    	 	|  	‘if’ expr stmt_list { ‘elseif’ expr stmt_list } [ ‘else’ stmt_list ] ‘end’
--  (6)    	 	|  	‘while’ expr stmt_list ‘end’
--  (7)    	 	|  	‘return’ expr
--  (8)    	 	|  	ID ( ‘(’ ‘)’ | [ ‘[’ expr ‘]’ ] ‘=’ expr )
--  (9)    	write_arg	  →  	‘cr’
--  (10)    	 	|  	STRLIT
--  (11)    	 	|  	expr
--  (12)    	expr	  →  	comp_expr { ( ‘&&’ | ‘||’ ) comp_expr }
--  (13)    	comp_expr	  →  	‘!’ comp_expr
--  (14)    	 	|  	arith_expr { ( ‘==’ | ‘!=’ | ‘<’ | ‘<=’ | ‘>’ | ‘>=’ ) arith_expr }
--  (15)    	arith_expr	  →  	term { ( ‘+’ | ‘-’ ) term }
--  (16)    	term	  →  	factor { ( ‘*’ | ‘/’ | ‘%’ ) factor }
--  (17)    	factor	  →  	‘(’ expr ‘)’
--  (18)    	 	|  	( ‘+’ | ‘-’ ) factor
--  (19)    	 	|  	NUMLIT
--  (20)    	 	|  	( ‘true’ | ‘false’ )
--  (21)    	 	|  	‘readnum’ ‘(’ ‘)’
--  (22)    	 	|  	ID [ ‘(’ ‘)’ | ‘[’ expr ‘]’ ]
--
--
-- All operators (&&, ||, ==, !=, <, <=, >, >=, binary +, binary -, *, /, %) are left-associative.
--
-- AST Specification
-- - For an ID, the AST is { SIMPLE_VAR, SS }, where SS is the string
--   form of the lexeme.
-- - For a NUMLIT, the AST is { NUMLIT_VAL, SS }, where SS is the string
--   form of the lexeme.
-- - For expr -> term, then AST for the expr is the AST for the term,
--   and similarly for term -> factor.
-- - Let X, Y be expressions with ASTs XT, YT, respectively.
--   - The AST for ( X ) is XT.
--   - The AST for X + Y is { { BIN_OP, "+" }, XT, YT }. For multiple
--     "+" operators, left-asociativity is reflected in the AST. And
--     similarly for the other operators.

local parseit = {}  -- Our module

local lexit = require "lexit"

-- Variables
-- For lexit iteration
local iter          -- Iterator returned by lexit.lex
local state         -- State for above iterator (maybe not used)
local lexit_out_s   -- Return value #1 from above iterator
local lexit_out_c   -- Return value #2 from above iterator

-- For current lexeme
local branch = false
local lexstr = ""   -- String form of current lexeme
local lexcat = 0    -- Category of current lexeme:
                    --  one of categories below, or 0 for past the end


-- Symbolic Constants for AST

-- String forms of symbolic constants

  local STMT_LIST = 1
  local WRITE_STMT = 2
  local FUNC_DEF = 3
  local FUNC_CALL = 4
  local IF_STMT = 5
  local WHILE_STMT = 6
  local RETURN_STMT = 7
  local ASSN_STMT = 8
  local CR_OUT = 9
  local STRLIT_OUT = 10
  local BIN_OP = 11
  local UN_OP = 12
  local NUMLIT_VAL = 13
  local BOOLLIT_VAL = 14
  local READNUM_CALL = 15
  local SIMPLE_VAR = 16
  local ARRAY_VAR = 17

-- Utility Functions

-- advance
-- Go to next lexeme and load it into lexstr, lexcat.
-- Should be called once before any parsing is done.
-- Function init must be called before this function is called.
local function advance()
    -- Advance the iterator
    lexit_out_s, lexit_out_c = iter(state, lexit_out_s)

    -- If we're not past the end, copy current lexeme into vars
    if lexit_out_s ~= nil then
        lexstr, lexcat = lexit_out_s, lexit_out_c
    else
        lexstr, lexcat = "", 0
    end
end


-- init
-- Initial call. Sets input for parsing functions.
local function init(prog)
    iter, state, lexit_out_s = lexit.lex(prog)
    advance()
end


-- atEnd
-- Return true if pos has reached end of input.
-- Function init must be called before this function is called.
local function atEnd()
    return lexcat == 0
end



-- matchString
-- Given string, see if current lexeme string form is equal to it. If
-- so, then advance to next lexeme & return true. If not, then do not
-- advance, return false.
-- Function init must be called before this function is called.
local function matchString(s)
    if lexstr == s then
        advance()
        return true
    else
        return false
    end
end


local function isLetter(lex)
    if ((lex > 'a' and lex < 'z') or (lex > 'A' and lex < 'Z')) then
        return true
    else
        return false
    end
end

-- matchCat
-- Given lexeme category (integer), see if current lexeme category is
-- equal to it. If so, then advance to next lexeme & return true. If
-- not, then do not advance, return false.
-- Function init must be called before this function is called.
local function matchCat(c)
    if lexcat == c then
        advance()
        return true
    else
        return false
    end
end


-- Primary Function for Client Code

-- "local" statements for parsing functions
local parse_expr
local parse_term
local parse_factor
local parse_stmt
local parse_stmt_list

-- parse
-- Given program, initialize parser and call parsing function for start
-- symbol. Returns pair of booleans & AST. First boolean indicates
-- successful parse or not. Second boolean indicates whether the parser
-- reached the end of the input or not. AST is only valid if first
-- boolean is true.
function parseit.parse(prog)
    -- Initialization
    init(prog)

    -- Get results from parsing
    local good, ast = parse_stmt_list()  -- Parse start symbol
    local done = atEnd()

    -- And return them
    return good, done, ast
end


-- Parsing Functions

-- Each of the following is a parsing function for a nonterminal in the
-- grammar. Each function parses the nonterminal in its name and returns
-- a pair: boolean, AST. On a successul parse, the boolean is true, the
-- AST is valid, and the current lexeme is just past the end of the
-- string the nonterminal expanded into. Otherwise, the boolean is
 -- false, the AST is not valid, and no guarantees are made about the
-- current lexeme. See the AST Specification near the beginning of this
-- file for the format of the returned AST.

-- NOTE. Declare parsing functions "local" above, but not below. This
-- allows them to be called before their definitions.

-- parse_stmt_list
-- Parsing function for nonterminal "stmt_list".
-- Function init must be called before this function is called.
function parse_stmt_list()
    local good, ast, newast

    ast = { STMT_LIST }
    while true do
        if lexstr ~= "write"
          and lexstr ~= "def"
          and lexstr ~= "if"
          and lexstr ~= "while"
          and lexstr ~= "return"
          and lexcat ~= lexit.ID then
            return true, ast
        end

        good, newast = parse_statement()
        if not good then
            return false, nil
        end

        table.insert(ast, newast)
    end
end

-- parse_statement
-- Parsing function for nonterminal "statement".
-- Function init must be called before this function is called.
function parse_statement()
    local good, ast, ast1, ast2, savelex
    savelex = lexstr

    --Parse function definitions
    if matchString("def") then
        savelex = lexstr
        if not matchCat(lexit.ID) or not matchString("(") or not matchString(")") then
            return false, nil
        else
            good, ast1 = parse_stmt_list()
            if good and matchString("end") then  
                return true, {FUNC_DEF, savelex, ast1}
            else
                return false, nil
            end
        end

    --Parse return
    elseif matchString("return") then 
        good, ast1 = parse_expr()
        if good then
            return true, {RETURN_STMT, ast1}
        else
            return false, nil
        end
    
    --Parse write
    elseif matchString("write") then
        if not matchString("(") then
            return false, nil
        end
        good, ast1 = parse_write_arg()
        if not good then
            return false, nil
        end
        ast2 = {WRITE_STMT, ast1}
        while matchString(",") do
            good, ast1 = parse_write_arg()
            if not good then
                return false, nil
            end
            table.insert(ast2, ast1)
        end
        if not matchString(")") then
            return false, nil
        else    
            return true, ast2
        end

    --Parse while
    elseif matchString("while") then
        good, ast1 = parse_expr()
        if not good then
            return false, nil
        end
        good, ast2 = parse_stmt_list()
        if not good then
            return false, nil
        end
        if matchString("end") then
            return true, {WHILE_STMT, ast1, ast2}
        else
            return false, nil
        end

    --Parse if
    elseif matchString("if") then
        good, ast1 = parse_expr()
        if good then 
            good, ast2 = parse_stmt_list()
        end
        if not good then
            return false, nil
        end
        ast = {IF_STMT, ast1, ast2}
        while matchString("elseif") do
            good, ast1 = parse_expr()
            if not good then 
                return false, nil
            end
            table.insert(ast, ast1)
            good, ast2 = parse_stmt_list()
            if not good then
                return false, nil
            end
            table.insert(ast, ast2)
        end
        if matchString("else") then
            good, ast1 = parse_stmt_list()
            if not good then
                return false, nil
            end
            table.insert(ast, ast1)
        end
        if matchString("end") then
            return true, ast
        end
        return false, nil
    
    --Parse IDs
    elseif matchCat(lexit.ID) then
        if matchString("(") then 
            if not matchString (")") then
                return false, nil
            end
            return true, {FUNC_CALL, savelex}
        elseif matchString("[") then
            good, ast1 = parse_expr()
            if not good 
                or not matchString("]") 
                or not matchString ("=") then
                return false, nil
            end
            good, ast2 = parse_expr()
            if not good then
                return false, nil
            end
            return true, {ASSN_STMT, {ARRAY_VAR, savelex, ast1}, ast2}
        else 
            if not matchString("=") then
                return false, nil
            end
            good, ast1 = parse_expr()
            if not good then
                return false, nil
            end
            return true, {ASSN_STMT, {SIMPLE_VAR, savelex}, ast1}
        end
    
    else
        return false, nil
    end
end
-- end Parse_statement()

-- Parse expressions
-- Function init must be called before this function is called.
function parse_expr()
    local good, ast1, ast2, savelex
    good, ast1 = parse_comp_expr()
    if not good then
        return false, nil
    end
    while true do
        savelex = lexstr
        if not matchString("&&") and not matchString("||") then 
            break
        end
        good, ast2 = parse_comp_expr()
        if not good then 
            return false, nil
        end
        ast1 = {{BIN_OP , savelex}, ast1, ast2}
    end
    return true, ast1
end

-- Parse compound expressions
-- Function init must be called before this function is called.
function parse_comp_expr()
    local good, ast1, ast2, savelex
    if matchString("!") then
        good, ast1 = parse_comp_expr()
        if not good then 
            return false, nil
        end
        return true, {{UN_OP, "!"}, ast1}
    else
        good, ast1 = parse_arith_expr()
        if not good then
            return false, nil
        end
        while true do
            savelex = lexstr
            if not matchString("<") 
                and not matchString(">")
                and not matchString("<=")
                and not matchString(">=")
                and not matchString("==")
                and not matchString("!=") then
                    break
            end
            good, ast2 = parse_arith_expr()
            if not good then
               return false, nil
            end
            ast1 = {{BIN_OP, savelex}, ast1, ast2}
        end
        return true, ast1
    end
end

-- Parse arithmetic expressions
-- Function init must be called before this function is called.
function parse_arith_expr()
    local good, ast1, ast2, savelex
    good, ast1 = parse_term()
    if not good then
        return false, nil
    end
    while true do
        savelex = lexstr
        if not matchString("+") and not matchString("-") then
            break
        end
        good, ast2 = parse_term()
        if not good then
            return false, nil
        end
        ast1 = {{BIN_OP, savelex}, ast1, ast2}
    end
    return true, ast1
end 

-- Parse Terms
-- Function init must be called before this function is called.
function parse_term()
    local good, ast1, ast2, savelex
    good, ast1 = parse_factor()
    if not good then
        return false, nil
    end
    while true do
        savelex = lexstr
        if not matchString('/') and not matchString('*')
            and not matchString('%') then
                break
        end
        good, ast2 = parse_factor()
        if not good then
            return false, nil
        end
        ast1 = {{BIN_OP, savelex}, ast1, ast2}
    end
    return true, ast1
end

-- Parse factors
-- Function init must be called before this function is called.
function parse_factor()
    local good, ast1, savelex
    savelex = lexstr

    if matchString("(") then
        good, ast1 = parse_expr()
        if not good or not matchString(")") then
            return false, nil
        end
        return true, ast1
    elseif matchString("readnum") then
        if not matchString("(") or not matchString(")") then
            return false, nil
        end
        return true, { READNUM_CALL }
    elseif matchString("+") or matchString("-") then
        good, ast1 = parse_factor()
        if not good then
            return false, nil     
        end
        return true, {{UN_OP, savelex}, ast1}
    elseif matchString("true") or matchString("false") then
        return true, {BOOLLIT_VAL, savelex}
    elseif matchCat(lexit.NUMLIT) then
        return true, {NUMLIT_VAL, savelex}
    elseif matchCat(lexit.ID) then
        if matchString("(") then 
            if not matchString(")") then
                return false, nil
            end
            return true, {FUNC_CALL, savelex}
        elseif matchString("[") then
            good, ast1 = parse_expr()
            if not good or not matchString("]") then
                return false, nil
            end
            return true, {ARRAY_VAR, savelex, ast1}
        else 
            return true, {SIMPLE_VAR, savelex}
        end
    else
        return false, nil
    end
end

-- Parse write arguments
-- Function init must be called before this function is called.
function parse_write_arg()
    local good, ast, savelex
    savelex = lexstr
    if matchCat(lexit.STRLIT) then
        return true, {STRLIT_OUT, savelex}
    elseif matchString("cr") then
        return true, {CR_OUT}
    else
        good, ast = parse_expr()
        if not good then 
            return false, nil
        end
        return true, ast
    end
end

-- Module Export

return parseit

