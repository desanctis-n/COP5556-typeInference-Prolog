:- begin_tests(typeInf).
:- include(typeInf). 

/* Note: when writing tests keep in mind that 
    the use of of global variable and function definitions
    define facts for gvar() predicate. Either test
    directy infer() predicate or call
    delegeGVars() predicate to clean up gvar().
*/

% tests for typeExp
test(typeExp_iplus) :- 
    typeExp(iplus(int,int), int).

% this test should fail
test(typeExp_iplus_F, [fail]) :-
    typeExp(iplus(int, int), float).

test(typeExp_iplus_T, [true(T == int)]) :-
    typeExp(iplus(int, int), T).

% NOTE: use nondet as option to test if the test is nondeterministic

% test for statement with state cleaning
test(typeStatement_gvar, [nondet, true(T == int)]) :- % should succeed with T=int
    deleteGVars(), /* clean up variables */
    typeStatement(gvLet(v, T, iplus(X, Y)), unit),
    assertion(X == int), assertion( Y == int), % make sure the types are int
    gvar(v, int). % make sure the global variable is defined

% same test as above but with infer 
test(infer_gvar, [nondet]) :-
    infer([gvLet(v, T, iplus(X, Y))], unit),
    assertion(T==int), assertion(X==int), assertion(Y=int),
    gvar(v,int).

% test custom function with mocked definition
test(mockedFct, [nondet]) :-
    deleteGVars(), % clean up variables since we cannot use infer
    asserta(gvar(my_fct, [int, float])), % add my_fct(int)-> float to the gloval variables
    typeExp(my_fct(X), T), % infer type of expression using or function
    assertion(X==int), assertion(T==float). % make sure the types infered are correct

% ~~~~~~~~~~~~~~~~ BEGIN MY TESTS ~~~~~~~~~~~~~~~~~

% typeExp infers integer addition as int
test(typeExp_iplus_T, [true(T == int)]) :-
    typeExp(iplus(int, int), T).

% typeExp rejects bad integer addition argument types
test(typeExp_iplus_bad_arg, [fail]) :-
    typeExp(iplus(float, int), _T).

% typeExp infers print as unit
test(typeExp_print_T, [true(T == unit)]) :-
    typeExp(print(string), T).

% functionType finds a built-in function signature
test(functionType_builtin, [true(T == [int, int, int])]) :-
    functionType(iplus, T).

% functionType does not treat a global variable as a function
test(functionType_global_var_not_function, [fail]) :-
    deleteGVars(),
    asserta(gvar(x, int)),
    functionType(x, _T).

% paramTypes get types from param declarations
test(paramTypes_two_params, [true(T == [int, float])]) :-
    paramTypes([k:int, i:float], T).

% infer gets integer expression type
test(infer_expr_int_plus, [true(T == int), nondet]) :-
    infer([expr(iplus(int, int))], T).

% infer gets float expression type
test(infer_expr_float_plus, [true(T == float), nondet]) :-
    infer([expr(fplus(float, float))], T).

% infer rejects incorrect integer params
test(infer_bad_int_plus, [fail]) :-
    infer([expr(iplus(float, int))], _T).

% infer computes boolean comparison type
test(infer_int_less_than, [true(T == bool), nondet]) :-
    infer([expr(i_LT(int, int))], T).

% infer computes boolean AND type
test(infer_bool_and, [true(T == bool), nondet]) :-
    infer([expr(b_AND(bool, bool))], T).

% infer defines a global variable
test(infer_global_var_def, [true(T == unit), nondet]) :-
    infer([gvLet(x, int, int)], T).

% infer uses a global variable
test(infer_global_var_use, [true(T == int), nondet]) :-
    infer([gvLet(x, int, int), expr(x)], T).

% infer rejects a global variable with a bad initializer
test(infer_global_var_bad_init, [fail]) :-
    infer([gvLet(x, int, float)], _T).

% infer handles return of an expression
test(infer_return_expression, [true(T == int), nondet]) :-
    infer([return(iplus(int, int))], T).

% infer rejects return of a bad expression
test(infer_return_bad_expression, [fail]) :-
    infer([return(iplus(float, int))], _T).

% infer handles an if statement returning int
test(infer_if_int, [true(T == int), nondet]) :-
    infer([if(i_LT(int, int), [expr(int)], [expr(iplus(int, int))])], T).

% infer rejects an if statement with a non-bool condition
test(infer_if_bad_condition, [fail]) :-
    infer([if(int, [expr(int)], [expr(int)])], _T).

% infer rejects an if statement with mismatched branch types
test(infer_if_branch_mismatch, [fail]) :-
    infer([if(i_LT(int, int), [expr(int)], [expr(float)])], _T).

% infer handles letIn local variable use
test(infer_letIn_int, [true(T == int), nondet]) :-
    infer([letIn(x, int, int, [expr(iplus(x, int))])], T).

% infer rejects letIn initializer type mismatch
test(infer_letIn_init_mismatch, [fail]) :-
    infer([letIn(x, int, float, [expr(x)])], _T).

% infer proves letIn locals do not leak
test(infer_letIn_no_leak, [fail]) :-
    infer([letIn(x, int, int, [expr(x)]), expr(x)], _T).

% infer handles a for loop with print body
test(infer_for_loop_print, [true(T == unit), nondet]) :-
    infer([for(i, int, int, [expr(print(i))])], T).

% infer rejects a for loop with bad start bound
test(infer_for_bad_start_bound, [fail]) :-
    infer([for(i, float, int, [expr(print(i))])], _T).

% infer shows loop variable does not leak
test(infer_for_no_leak, [fail]) :-
    infer([for(i, int, int, [expr(print(i))]), expr(i)], _T).

% infer handles code block returning int
test(infer_block_int, [true(T == int), nondet]) :-
    infer([block([expr(print(string)), expr(iplus(int, int))])], T).

% infer rejects block when not a list
test(infer_block_bad_not_list, [fail]) :-
    infer([block(expr(int))], _T).

% infer calls global function
test(infer_gFnDef_call_add, [true(T == int), nondet]) :-
    infer([gFnDef(add, [x:int, y:int], int, [return(iplus(x, y))]), expr(add(int, int))], T).

% infer rejects a function with bad return type
test(infer_gFnDef_bad_return_type, [fail]) :-
    infer([gFnDef(bad, [x:int], int, [return(float)])], _T).

% infer shows function params do not leak
test(infer_gFnDef_param_does_not_leak, [fail]) :-
    infer([gFnDef(add, [x:int, y:int], int, [return(iplus(x, y))]), expr(x)], _T).

% ~~~~~~~~~~~~~ TEST BUILTINS ~~~~~~~~~~~~
% These basically don't count, but I'm putting them in for complete coverage
% using nondet because it will complain about choicepoint otherwise

% infer does integer multiplication
test(infer_builtin_imul, [true(T == int), nondet]) :-
    infer([expr(imul(int, int))], T).

% infer does integer division
test(infer_builtin_idiv, [true(T == int), nondet]) :-
    infer([expr(idiv(int, int))], T).

% infer does integer <
test(infer_builtin_i_LT, [true(T == bool), nondet]) :-
    infer([expr(i_LT(int, int))], T).

% infer does integer >
test(infer_builtin_i_GT, [true(T == bool), nondet]) :-
    infer([expr(i_GT(int, int))], T).

% infer does integer <=
test(infer_builtin_i_LE, [true(T == bool), nondet]) :-
    infer([expr(i_LE(int, int))], T).

% infer does integer >=
test(infer_builtin_i_GE, [true(T == bool), nondet]) :-
    infer([expr(i_GE(int, int))], T).

% infer does integer equality
test(infer_builtin_i_EQ, [true(T == bool), nondet]) :-
    infer([expr(i_EQ(int, int))], T).

% infer does float multiplication
test(infer_builtin_fmul, [true(T == float), nondet]) :-
    infer([expr(fmul(float, float))], T).

% infer does float division
test(infer_builtin_fdiv, [true(T == float), nondet]) :-
    infer([expr(fdiv(float, float))], T).

% infer does float <
test(infer_builtin_f_LT, [true(T == bool), nondet]) :-
    infer([expr(f_LT(float, float))], T).

% infer does float >
test(infer_builtin_f_GT, [true(T == bool), nondet]) :-
    infer([expr(f_GT(float, float))], T).

% infer does float <=
test(infer_builtin_f_LE, [true(T == bool), nondet]) :-
    infer([expr(f_LE(float, float))], T).

% infer does float >=
test(infer_builtin_f_GE, [true(T == bool), nondet]) :-
    infer([expr(f_GE(float, float))], T).

% infer does float ==
test(infer_builtin_f_EQ, [true(T == bool), nondet]) :-
    infer([expr(f_EQ(float, float))], T).

% infer does bool AND
test(infer_builtin_b_AND, [true(T == bool), nondet]) :-
    infer([expr(b_AND(bool, bool))], T).

% infer does bool OR
test(infer_builtin_b_OR, [true(T == bool), nondet]) :-
    infer([expr(b_OR(bool, bool))], T).

% infer does bool NOT
test(infer_builtin_b_NOT, [true(T == bool), nondet]) :-
    infer([expr(b_NOT(bool))], T).

% infer does bool XOR
test(infer_builtin_b_XOR, [true(T == bool), nondet]) :-
    infer([expr(b_XOR(bool, bool))], T).

:-end_tests(typeInf).
