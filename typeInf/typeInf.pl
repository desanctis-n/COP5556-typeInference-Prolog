/* this is a predicate modified at runtime, it should be declared dynamic */
:- dynamic gvar/2.

/* match functions by unifying with arguments 
    and infering the result
*/
typeExp(Fct, T):-
    \+ var(Fct), /* make sure Fct is not a variable */ 
    \+ atom(Fct), /* or an atom */
    functor(Fct, Fname, _Nargs), /* ensure we have a functor */
    !, /* if we make it here we do not try anything else */
    Fct =.. [Fname|Args], /* get list of arguments */
    append(Args, [T], FType), /* make it loook like a function signature */
    functionType(Fname, TArgs), /* get type of arguments from definition */
    typeExpList(FType, TArgs). /* recurisvely match types */

/* lookup by name next */
typeExp(Name, T):-
    atom(Name), /* if it's an atom */
	gvar(Name, T). /* if it's a global */

/* propagate types */
typeExp(T, T):-
    bType(T). /* yeah, only match known types, not random stuff */

/* MAYBE TODO: does the above need to be modified? (YES) */

/* list version to allow function mathine */
typeExpList([], []).
typeExpList([Hin|Tin], [Hout|Tout]):-
    typeExp(Hin, Hout), /* type infer the head */
    typeExpList(Tin, Tout). /* recurse */

/* TODO: add statements types and their type checking */
/* global variable definition
    Example:
        gvLet(v, T, int) ~ let v = 3;
 */

/* rule to remove references from database */
deleteRefs([]). /* base case */
deleteRefs([Ref|Refs]):-
    erase(Ref), /* yeet */
	deleteRefs(Refs). /* recurse */

/* temporarily insert params as known variables */
bindParams([], []). /* base case */
bindParams([Name:T|Params], [Ref|Refs]):-
    atom(Name), /* should be an atom */
	bType(T), /* should be a valid type */
	asserta(gvar(Name, T), Ref), /* add param to type environment */
	bindParams(Params, Refs). /* recurse */

/* extract types from function params */
paramTypes([], []). /* base case */
paramTypes([_Name:T|Params], [T|Types]):- /* match the first parameter, don't care about name */
    bType(T), /* should be a valid type */
	paramTypes(Params, Types). /* recurse */

typeStatement(gvLet(Name, T, Code), unit):-
    atom(Name), /* make sure we have a bound name */
    typeExp(Code, T), /* infer the type of Code and ensure it is T */
    bType(T), /* make sure we have an infered type */
    asserta(gvar(Name, T)). /* add definition to database */

/* add expression statements */
typeStatement(expr(Code), T):-
    typeExp(Code, T). /* let bare expression be used as statement */

/* add return statements */
typeStatement(return(Code), T):-
    typeExp(Code, T). /* value being returned */

/* if statements: condition, then code, else code */
typeStatement(if(Cond, Then, Else), T):-
    typeExp(Cond, bool), /* it had better be a bool */
	is_list(Then), /* make sure Code is a list */
	is_list(Else), /* make sure Code is a list */
	typeCode(Then, T), /* then branch -> code */
	typeCode(Else, T). /* else branch -> code */

/* let in statements: name (local), type of local, initializer expression, code block */
typeStatement(letIn(Name, T, Init, Block), BlockType):-
    atom(Name), /* make sure we have a bound name */
	is_list(Block), /* make sure Code is a list */
	typeExp(Init, T),  /* make sure init declared with type T */
	bType(T), /* make sure T is a valid type */
	asserta(gvar(Name, T), Ref), /* temporarily add local to the environment */
	(typeCode(Block, BlockType), erase(Ref) /* disjunction: either block typechecks, then erase the local */
	; /* or */
	erase(Ref), fail). /* erase and fail */

/* for statements: name (local), start expression, end expression, code block */
typeStatement(for(Name, Start, End, Block), unit):-
    atom(Name), /* make sure we have a bound name */
	is_list(Block), /* make sure Code is a list */
	typeExp(Start, int), /* index based loop, must be int */
	typeExp(End, int),
	asserta(gvar(Name, int), Ref), /* temporarily add loop variable to environment as an int */
	(typeCode(Block, _Type), erase(Ref) /* disjunction: either block typechecks (don't care about type), then erase the local */
	; /* or */
	erase(Ref), fail). /* erase and fail */

/* code blocks: just a list of code */
/* does this support ';' as a delimiter? */
typeStatement(block(Code), T):-
    is_list(Code), /* single statement not a block */
	typeCode(Code, T).

/* global function definition: function name, list of param names/types, return type, function body (code block) */
typeStatement(gFnDef(Name, Params, RetT, Block), unit):-
    atom(Name), /* make sure we have a bound name */
	is_list(Params), /* make sure params is list */
	is_list(Block), /* make sure block is list of statements? */
	paramTypes(Params, ParamTypes), /* pull out the types */
	append(ParamTypes, [RetT], FnSig), /* make the function signature */
	bType(FnSig), /* it had better be a valid type */
	asserta(gvar(Name, FnSig), FnRef), /* temporarily add function to environment */
	
	(bindParams(Params, ParamRefs), /* temporarily add param bindings */
	typeCode(Block, RetT), /* make sure it returns the right thing */
	deleteRefs(ParamRefs), /* drop refs from database */
	erase(FnRef), /* remove the temp binding */
	asserta(gvar(Name, FnSig)) /* add the binding permanently */
	; /* otherwise, clean up and fail */
	erase(FnRef),
	fail).


/* Code is simply a list of statements. The type is 
    the type of the last statement 
*/
typeCode([S], T):-typeStatement(S, T).
typeCode([S, S2|Code], T):-
    typeStatement(S,_T),
    typeCode([S2|Code], T).

/* top level function */
infer(Code, T) :-
    is_list(Code), /* make sure Code is a list */
    deleteGVars(), /* delete all global definitions */
    typeCode(Code, T).

/* Basic types
    TODO: add more types if needed
 */
bType(int).
bType(float).
bType(string).
bType(bool).
bType(unit). /* unit type for things that are not expressions */
/*  functions type.
    The type is a list, the last element is the return type
    E.g. add: int->int->int is represented as [int, int, int]
    and can be called as add(1,2)->3
 */
bType([H]):- bType(H).
bType([H|T]):- bType(H), bType(T).

/*
    TODO: as you encounter global variable definitions
    or global functions add their definitions to 
    the database using:
        asserta( gvar(Name, Type) )
    To check the types as you encounter them in the code
    use:
        gvar(Name, Type) with the Name bound to the name.
    Type will be bound to the global type
    Examples:
        g

    Call the predicate deleveGVars() to delete all global 
    variables. Best wy to do this is in your top predicate
*/

/* deleteGVars():-retractall(gvar), asserta(gvar(_X,_Y):-false()). */
deleteGVars():-retractall(gvar(_,_)). /* needs to delete gvar facts with 2 predicates */

/*  builtin functions
    Each definition specifies the name and the 
    type as a function type

    TODO: add more functions
*/

fType(iplus, [int,int,int]).
fType(fplus, [float, float, float]).
fType(fToInt, [float,int]).
fType(iToFloat, [int,float]).
fType(print, [_X, unit]). /* simple print */

/* more built ins */
/* ints */
fType(imul, [int, int, int]).
fType(idiv, [int, int, int]).
fType(i_LT, [int, int, bool]).
fType(i_GT, [int, int, bool]).
fType(i_LE, [int, int, bool]).
fType(i_GE, [int, int, bool]).
fType(i_EQ, [int, int, bool]).
/* floats */
fType(fmul, [float, float, float]).
fType(fdiv, [float, float, float]).
fType(f_LT, [float, float, bool]).
fType(f_GT, [float, float, bool]).
fType(f_LE, [float, float, bool]).
fType(f_GE, [float, float, bool]).
fType(f_EQ, [float, float, bool]).
/* bools */
fType(b_AND, [bool, bool, bool]).
fType(b_OR, [bool, bool, bool]).
fType(b_NOT, [bool, bool]).
fType(b_XOR, [bool, bool, bool]).

/* Find function signature
   A function is either buld in using fType or
   added as a user definition with gvar(fct, List)
*/

% Check the user defined functions first
functionType(Name, Args):-
    gvar(Name, Args),
    is_list(Args). % make sure we have a function not a simple variable

% Check first built in functions
functionType(Name, Args) :-
    fType(Name, Args), !. % make deterministic

% This gets wiped out but we have it here to make the linter happy
gvar(_, _) :- false().
