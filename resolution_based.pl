

:- op(300,fx,@). /*@K*/
:- op(400,fx,$). /*$B*/

:- op(500,fx,-).
%:- op(500,fx,~).
:- op(780,xfy,&).
:- op(790,xfy,\/).%/
:- op(800,xfy,->).
:- op(800,xfy,<->).

%-----------define the dynamic predicts------------------
:- dynamic(prop/1).
:- dynamic(klist/1).
:- dynamic(blist/1).
:- dynamic(pair/2).

%---------------------end define---------------------------

ksnc :-
	write("Please input the txt file name!\n"),
	open('Cresult.txt', write, Str), %trace, 
	%generate_KBterm(Clause_num), %trace, 
	read_formula(Formula1, P, Q), %trace, write("Formula="), write(Formula1), nl,
	%random(1, Variable_n, Q),
	%generate_P(Variable_n, P),
	%generate_P_list(Variable_n, PN, P),
	%generate_list(1, Variable_n, L1),  %trace, write("L1="), write(L1), nl, %generate the set of prop in formula.
	Formula = (Formula1 & Q), write("formula="), write(Formula), 
	gain_prop(Formula, PN1), write("PN1="), write(PN1), nl, 
	add_propTerm(PN1), append(PN1, [Q],OP), write("OP="), write(OP), nl, 
	difference_list(P, OP, P1), sort(P1, P2), write("P2="), write(P2), nl, %!, trace, 
	kForget1(Formula, P2, SNC),
	write("P="), write(P), nl,
	write("Q="), write(Q), nl,
	write("P1="), write(P2), nl,
	write("T="), write(Formula1), nl,
	write(Str,'P='), write(Str, P), nl(Str), %write(Str,"\n"),
	write(Str,'Q='), write(Str, Q), nl(Str), %write(Str,"\n"),
	write(Str,'P1='), write(Str, P2), nl(Str), %write(Str,"\n"),
	write(Str,'Theory='), write(Str, Formula1), nl(Str), %write(Str,"\n"),
	write(Str, 'SNC is: '), write(Str, SNC), nl(Str), %write(Str,"\n"),
	write(Str,'...............................................'), nl(Str),
	retractall(prop(X)),
	close(Str).

	
%------------------------read formula from file----------------
%read formula from file and assert the atom which in formula
read_formula(Formula, P, Q) :- write_ln('input: '), read(user_input,Input), %consult(Input),
	string_concat(Input, '.txt', Filename1),
	string_to_atom(Filename1, Filename),
	read_file(Filename, Formula, P, Q).


read_file(Filename, [],P,Q) :- open(Filename, read, Str), at_end_of_stream(Str), write("there is no formula\n"), !.
read_file(Filename, Formula, P, Q) :-
	open(Filename, read, Str),
	read(Str, Formula),
	read(Str, Q),
	read(Str, P),
	close(Str).
	%read_prop(Str).


read_prop(Str) :-
    read_prop_list(Str, X),
    close(Str).

read_prop_list(Stream, []) :-
	at_end_of_stream(Stream).


read_prop_list(Stream, [X|L]) :-
    \+ at_end_of_stream(Stream),
    read(Stream, X),
    assert(X),
    read_prop_list(Stream, L).

%--------------end read formula---------------------

%-----------------------snc-------------------------------
%the SNC of Q on P under Formula is kForget(Formula & Q, Var(Formula & Q)-P)
%P1 = Var(Formula & Q)-P
snc(Q, P, Formula, SNC) :- gain_prop(Formula, PN1), write("PN1="), write(PN1), nl, 
	add_propTerm(PN1), append(PN1, [Q],OP), write("OP="), write(OP), nl, 
	difference_list(P, OP, P1), write("P1="), write(P1), nl, 
	kForget(Formula, P1, SNC), 
	retractall(prop(X)).

%----------------end--------------------------------------

% prop cope with 
add_prop(N) :- N=0, assert(prop(N)), !.
add_prop(N) :- assert(prop(N)), N1 is N-1, add_prop(N1).

%gain the atom of a formula
gain_prop(P & Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), 
	unionSet(L1, L2, L).
gain_prop(P \/ Q, L) :- gain_prop(P, L1), gain_prop(Q, L2), %/
	unionSet(L1, L2, L).
gain_prop(@P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(-P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop($P, L) :- gain_prop(P, L1), sort(L1, L).
gain_prop(P, [P]) :- \+ atom(P), !.

%compute the union of two sets
unionSet(L1, L2, L) :- append(L1, L2, L11), sort(L11, L).

add_propTerm([]) :- !.
add_propTerm([X|L]) :- assert(prop(X)), add_propTerm(L).


%------------------add-------------------------
equall(P, P) :- prop(P), !.
equall(-P, -P) :- prop(P), !.
equall(-(-P), P) :- prop(P), !.


kclause_true(C, Flag) :- C = kclause(Cclause, KT, BT),
	judge_Cclause(Cclause, Flag1),
	judge_KT(KT, Flag2),
	judge_BT(BT, Flag3),
	((Flag1 == true; Flag2 == true; Flag3 == true), Flag = true; Flag = false).

judge_Cclause(Clause, Flag) :- (member([], Clause), Flag = true; Flag = false).

judge_KT(KT, Flag) :- (member([[]], KT), Flag = true; Flag = false).

judge_BT(BT, Flag) :- (member([], BT), Flag = true; Flag = false).



%Supp: eliminat the atoms which will be forgten from the result of kforget.
%Supp(P,C∨KD1∨…∨KDn∨BE1∨….∨BEr )=C∨K(Supp(P,D1))∨…∨K(Supp(P,Dn))∨B(Supp(P,E1))∨…∨B(Supp(P,Er))
%Supp(P,Ei )={Supp(P,X)|X∈Ei}

supp([], _, []) :- !.
supp(A, [], A) :- !.
supp([X|L], LP, L1) :- supp_one(X, LP, NewC, Flag), 
	Flag == true, supp(L, LP, L1).
supp([X|L], LP, [NewC|L1]) :- supp_one(X, LP, NewC, Flag), 
	Flag == false, supp(L, LP, L1).



supp_one(X, [], X, false) :- !.
supp_one(X, [P|LP], Y, Flag) :- supp_oneA(X, P, NewC, Flag1), 
	(Flag1 == true, (Flag = true, Y = NewC); supp_one(NewC, LP, Y, Flag)), !.

supp_oneA(C, P, _, true) :- C = kclause(Cclause, KT, BT), 
	(member(P, Cclause); member(-P, Cclause)), !.
supp_oneA(C, P, NewC, Flag) :- C = kclause(Cclause, KT, BT), 
	suppKT(KT, P, NewKT, Flag1), suppBT(BT, P, NewBT, Flag2),
	NewC = kclause(Cclause, NewKT, NewBT),
	((Flag1 = false, Flag2 = false), Flag = false; Flag = true), !.

suppKT([], _, [], Flag) :- Flag = false, !.
suppKT(KT, P, KT, Flag) :- \+ findPTerm(KT, P, X), \+ findPTerm(KT, -P, Y), Flag = false.
suppKT(KT, P, [], Flag) :- (findPTerm(KT, P, X); findPTerm(KT, -P, Y)), Flag = true.


suppBT([], _, [], Flag) :- Flag = false, !.
suppBT(BT, P, BT, Flag) :- \+ findPTerm(BT, P, X), \+ findPTerm(BT, -P, Y), Flag = false.
suppBT(BT, P, NewBT, Flag) :- findPTerm(BT, P, X), delete_X(X, P, F1), 
	(F1 = [], (Flag = true, NewBT = []); 
	delete(BT, X, NewBT1), append([F1], NewBT1, NewBT2), suppBT(NewBT2, P, NewBT, Flag)).
suppBT(BT, P, NewBT, Flag) :- findPTerm(BT, -P, X), delete_X(X, -P, F1), 
	(F1 = [], (Flag = true, NewBT = []); 
	delete(BT, X, NewBT1), append([F1], NewBT1, NewBT2), suppBT(NewBT2, P, NewBT, Flag)).


delete_X([], _, []) :- !.
delete_X([X|L1], P, L) :- (member(P, X); member(-P, X)), delete_X(L1, P, L).
delete_X([X|L1], P, [X|L2]) :- \+ member(P, X), \+ member(-P, X), delete_X(L1, P, L2).

%----------------------------end----add------------------------

%------------------------read formula from file----------------
readFandP(Filename1, Formula) :- 
		string_concat(Filename1, '.txt', Filename11),
		string_to_atom(Filename11, Filename),
		open(Filename, read, Str1),
		read_file(Str1, Formula),
		close(Str1),
		write("read 1"), nl.

elim0([], []).
elim0([X|L], [X|R]) :- not(X==0), elim0(L, R).
elim0([X|L], R) :- elim0(L, R).
		
		
gain(Str, []) :- at_end_of_stream(Str).
gain(Str, FP) :-
	not(at_end_of_stream(Str)),
	read(Str, Formula),
	gain_list(Str, FP).	
	
gain_list(Stream, []) :-  at_end_of_stream(Stream).
gain_list(Stream, [P|L]) :-
    not(at_end_of_stream(Stream)),
    read(Stream, X),
    prop(Y) = X, 
	(prop(Y), (P=Y, gain_list(Stream, L)); P=0, gain_list(Stream, L)), !.

		
read_file(Str, []) :-  at_end_of_stream(Str), write("there is no formula\n"), !.
read_file(Str, Formula) :-
	not(at_end_of_stream(Str)),
	read(Str, Formula),
	read_prop(Str).
	

read_prop(Str) :-
	 at_end_of_stream(Str). 
read_prop(Str) :-
	not(at_end_of_stream(Str)),
    read_prop_list(Str, X).
    

	
read_prop_list(Stream, _) :-
	at_end_of_stream(Stream).
read_prop_list(Stream, [X|L]) :-
    not(at_end_of_stream(Stream)),
    read(Stream, X),
    assert(X),
    read_prop_list(Stream, L).

%--------------end read formula---------------------


%-------------generate P---------------------------
%generate the set with a random number of prop randomly and |P| >= 1.
generate_P(Variable_n, L) :- random(1, Variable_n, N),
	generate_P_list(Variable_n, N, L).

generate_P_list(Variable_n, 0, []) :- !.
generate_P_list(Variable_n, N, [X|L]) :-
	random(1, Variable_n, X),
	N1 is N-1,
	generate_P_list(Variable_n, N1, L).


%generate a list L which is no-repeat and the length of it is N
genPlist(Variable_n, 0, [], Or) :- !.
genPlist(Variable_n, N, [X|L], Or) :-
	random(1, Variable_n, X),
	(\+ (member(X, Or)), (N1 is N-1, append([X],Or, Or1)); N1 is N, Or = Or1),
	genPlist(Variable_n, N1, L, Or1).

%----------------end-----------------------------------------

%------------------output the time of solving a problem-----------
time_output_1(Goal, UsedInf,UsedTime,Wall) :-
	time_state(State0),
	call(Goal),
	report_output(State0, 11, UsedInf, UsedTime, Wall).

report_output(t(OldWall, OldTime, OldInferences), Sub, UsedInf,UsedTime,Wall) :-
	time_state(t(NewWall, NewTime, NewInferences)),
	UsedTime is NewTime - OldTime,
	UsedInf  is NewInferences - OldInferences - Sub,
	Wall     is NewWall - OldWall,
	(   UsedTime =:= 0
	->  Lips = 'Infinite'
	;   Lips is integer(UsedInf / UsedTime)
	),
	print_message(information, time(UsedInf, UsedTime, Wall)).


time_state(t(Wall, Time, Inferences)) :-
	get_time(Wall),
	statistics(cputime, Time),
	statistics(inferences, Inferences).
/*
time_true(State0) :-
	report_output(State0, 12, X, Y, Z).		% leave choice-point
time_true(State) :-
	get_time(Wall),
	statistics(cputime, Time),
	statistics(inferences, Inferences0),
	plus(Inferences0, -3, Inferences),
	nb_setarg(1, State, Wall),
	nb_setarg(2, State, Time),
	nb_setarg(3, State, Inferences),
	fail.*/

%------------------------- end -------------------------------


%-------------action consquent delete--------------
cons_delet :- retractall(pair(_,_)),
	retractall(klist(_)),
	retractall(blist(_)).

	
%--------------------end-----------------------------

test(F, P, L1, L2, L3, L4,L5) :- mcnf2list(F, List), write(List), nl, 
	split_p(List, P, L1, L2, L3, L4,L5, L6).
	
%----------------------------kForget----------------------------------------
%kForget(F,[],F) :- !.
%kForget(F, LP, NEW) :- mcnf2list(F, List), write("List"),write(List),nl, kforget(List, LP, NEW1), supp(NEW1, LP, NEW).

kForget1(F,[],F) :- !.
kForget1(F, LP, NEW) :- mcnf2Lst(F, List),  write("List"),write(List),nl,
	find_P1(List, LP, List1),
	difference_list(List1, List, List2),
	kforget(List2, LP, NEW1), 
	supp(NEW1, LP, NEW2), 
	append(NEW2, List1, NEWK), kcnf2Kwff(NEWK, NEW).
kForget1(F, LP, NEW) :- mcnf2Lst(F, List), supp(List, LP, NEWK), kcnf2Kwff(NEWK, NEW).

kForget(F,[],F) :- !.
kForget(F, LP, NEW) :- mcnf2list(F, List),  write("List"),write(List),nl,
	find_P1(List, LP, List1),
	difference_list(List1, List, List2),
	kforget(List2, LP, NEW1), 
	supp(NEW1, LP, NEW2), 
	append(NEW2, List1, NEWK), kcnf2Kwff(NEWK, NEW).
kForget(F, LP, NEW) :- mcnf2list(F, List), supp(List, LP, NEWK), kcnf2Kwff(NEWK, NEW).

/*kForget(F,[],F) :- !.
kForget(F, LP, NEW) :- mcnf2list(F, List), %write("List"),write(List),nl, 
	find_P1(List, LP, List1),
	difference_list(List1, List, List2),
	kforget(List2, LP, NEW1), 
	supp(NEW1, LP, NEW2), 
	append(NEW2, List1, NEW).
	%, kcnf2Kwff(NEWK, NEW).
kForget(F, LP, NEW) :- mcnf2list(F, List), supp(List, LP, NEW). %, kcnf2Kwff(NEWK, NEW).*/


%compute the result of forget some atoms(P) from formula with MDNF
kforget([],_, []) :- !.
kforget(A,[],A) :- !.
kforget(L, [P|LP], F) :-  kforget_one(L, P, F1),
	eliminate_subsum(F1, F1, F2), kforget(F1, LP, F), !. 

kforget_one([], _, _) :- !.
kforget_one(L, P, R) :-  fact_circle(L, NL), sort(NL, NewL),
	forget_all(NewL, P, F), 
	(F \= NewL, kforget_one(F, P, R); R = F), !.

%simplify kclause and eliminate true-kclause.
fact_circle([], []) :- !.
fact_circle([C|L], NL) :- fact(C, C1), kclause_true(C1, Flag), Flag == true, fact_circle(L, NL).
fact_circle([C|L], [C1|NL]) :- fact(C, C1), fact_circle(L, NL).

/*fact_circle([], []) :- !.
fact_circle([C|L], [C1|NL]) :- fact(C, C1), kclause_true(C1, Flag), \+ (Flag == true), fact_circle(L, NL), !.
fact_circle([C|L], NL) :- fact(C, C1), fact_circle(L, NL).*/


%------------------------------------eliminate_subsum-------------------------
%eliminate those clauses in L, that are subsumed by another one of the clause in L
eliminate_subsum([],L, L) :- !.
eliminate_subsum(_, [], []) :- !.
eliminate_subsum([X|L1], L2, L) :- delete(L2, X, L3), eliminate_subsum_one(X, L3, L11),
	(\+ bagof(Y, (member(Y, L3), \+ member(Y, L11)), AL), AL = [];
		bagof(Y, (member(Y, L3), \+ member(Y, L11)), AL)),
	(\+ bagof(Y1, (member(Y1, L1), \+ member(Y1, AL)), L12), L12 = [];
		bagof(Y1, (member(Y1, L1), \+ member(Y1, AL)), L12)),
	(\+ member(X, AL), eliminate_subsum(L12, [X|L11], L); eliminate_subsum(L12, L11, L)).


%eliminate the clause B, if A subsum B
eliminate_subsum_one(_, [], []) :- !.
eliminate_subsum_one(X, [Y|L1], [Y|L]) :- subsum_Kcl(X, Y, Flag),
	Flag == false, eliminate_subsum_one(X, L1, L).
eliminate_subsum_one(X, [Y|L2], L) :- eliminate_subsum_one(X, L2, L).

%judge whether C1 subsume C2, if so then Flag=true, else Flag=false.
subsum_Kcl(C1, C2, Flag) :- C1 = kclause(Cclause1, KT1, BT1),
	C2 = kclause(Cclause2, KT2, BT2),
	Cclause1=[Cclause11], Cclause2=[Cclause21],
	subsume_Ccl(Cclause11, Cclause21, Flag1),
	(Flag1=false, (subsume_CBT(Cclause1, BT2, Flag4), Flag11=Flag4); Flag11=Flag1),
	subsume_KT(KT1, KT2, Cclause21, BT2, Flag2),
	subsume_BT(BT1, BT2, Flag3),
	((Flag11=true, Flag2=true, Flag3=true), Flag=true; Flag = false), !.

%if Cc1 subsume Cc2, i.e Cc1 is a subset of Cc2, then Flag=true, else Flag=false.
subsume_Ccl(Cc1, Cc2, Flag) :-  (\+ (member(X,Cc1), \+ member(X,Cc2)), Flag = true; Flag = false).

%if exists Y in BT2, s.t. Cclause subsume Y, then Flag=true, else Flag=false.
subsume_CBT(Cclause, BT2, Flag) :- subsume_BT_list(Cclause, BT2, Flag), !.

%if for every X in KT1, exists Y in KT2, s.t X subsume Y, then Flag=true, else Flag=false.
subsume_KT([], _, Cclause21, BT2, true) :- !.
subsume_KT(_, [], Cclause21, BT2, false) :- !.
subsume_KT([X|KT1], KT2, Cclause21, BT2, Flag) :- subsume_KT_list(X, KT2, Flag1), 
	(Flag1=false, (subsume_KTC(X, Cclause21, Flag3), Flag11=Flag3); Flag11=Flag1),
	(Flag11=false, (subsume_KTBT(X, BT2, Flag4), Flag111=Flag4); Flag111=Flag11),
	subsume_KT(KT1, KT2, Cclause21, BT2, Flag2), ((Flag111=true, Flag2=true), Flag=true; Flag=false).

%if X subsume Cclause, then Flag=ture, else Flag=false.
subsume_KTC(X, Cclause, Flag) :- X=[Y], subsume_Ccl(Y, Cclause, Flag), !.

%if exists Y in BT2, s.t X subsume every elements in Y. This is similar with subsume_BT.
subsume_KTBT(X, BT2, Flag) :- subsume_BT_list(X, BT2, Flag), !.

% If exists Y in KT2 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_KT_list(X, [], false) :- !.
subsume_KT_list(X, [Y|KT2], Flag) :- X = [X1], Y = [Y1], subsume_Ccl(X1, Y1, Flag1),
	(Flag1=true, (Flag=true, !); subsume_KT_list(X, KT2, Flag)).

%if for every X in BT1, exists Y in BT2, s.t X subsume Y, then Flag=true, else Flag=false.
subsume_BT([], _, true) :- !.
subsume_BT(_, [], false) :- !.
subsume_BT([X|BT1], BT2, Flag) :- subsume_BT_list(X, BT2, Flag1),
	subsume_BT(BT1, BT2, Flag2), ((Flag1=true, Flag2=true), Flag=true; Flag=false).

% If exists Y in BT2 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_BT_list(X, [], false) :- !.
subsume_BT_list(X, [Y|BT2], Flag) :- subsume_bterm(X, Y, Flag1),
	(Flag1=true, (Flag=true, !); subsume_BT_list(X, BT2, Flag)).

%if for all Y in L2, exists X in L1 s.t X subsume Y, then Flag=true, else Flag=false.
subsume_bterm([], X, false) :- !.
subsume_bterm(_, [], true) :- !.
subsume_bterm(L1, [Y|L2], Flag) :- subsume_bterm_list(L1, Y, Flag1),
	subsume_bterm(L1, L2, Flag2), ((Flag1=true, Flag2=true), Flag=true; Flag=false).

subsume_bterm_list([], _, false) :- !.
subsume_bterm_list([X|L1], Y, Flag) :- subsume_Ccl(X, Y, Flag1),
	(Flag1=true, (Flag=true, !); subsume_bterm_list(L1, Y, Flag)).

%-----------------------------------end--------------------------


test(L, PL, L1) :- find_P1(L, PL, LP1), 
	eliminateIR(LP1, [kclause([[p,q]],[[[e,f]]],[[[r,t],[s]]]), kclause([[q]], [[[e]]], [[[r],[s],[p]]])], L1). 
%-----------------------find_P1-------------------
%find all the clause which doesn't include atoms in P.  '
find_P1(L, [], L) :- !.
find_P1([], _, []) :- !.
find_P1(L, [P|PL], NewL) :- split_p(L, P, L1, L2, L3, L4, L5, L6),
	find_P1(L6, PL, NewL).
%--------------------------end---------------------------------


%-------------------eliminateIR--------------------
%eliminate kclause C if it is subsumed by one of kclause in the union of LP1 and F-{C}.
eliminateIR(LP1, [], LP1) :- !.
eliminateIR([], F, F) :- !.
eliminateIR(LP1, [X|F], L) :- append(LP1, F, C1), eliminate_subsum(C1, C1, Ca),
	eliminateIR_list(Ca, X, Flag1),
	Flag1=true,
	eliminateIR(LP1, F, L).
eliminateIR(LP1, [X|F], [X|L]) :- append(LP1, F, C1), eliminate_subsum(C1, C1, Ca),
	eliminateIR_list(Ca, X, Flag1),
	Flag1=false, 
	eliminateIR(LP1, F, L).

eliminateIR_list([], _, false) :- !.
eliminateIR_list([X|L], Y, Flag) :- subsum_Kcl(X, Y, Flag1), 
	(Flag1=true, Flag=true; eliminateIR_list(L, Y, Flag)), !.

%------------------------end-------------------------------


forget_all([], _, []) :- !.
forget_all(L, P, F) :- split_p(L, P, L1, L2, L3, L4, L5, L6), 
	forget(L1, L2, P, F1), 
	forgetKB(L3, L4, P, F2), 
	forgetKB(L3, L5, P, F3), 
	forgetKB(L5, L4, P, F4),
	forgetK(L3, L2, P, F5),
	forgetK(L1, L4, P, F6),
	forgetK(L5, L2, P, F7),
	forgetK(L1, L5, P, F8),
	forgetKK(L3, L5, P, F9),
	forgetKK(L5, L4, P, F10),
	forgetKK(L3, L4, P, F11),
	forgetB(L5, P, F12),
	delete_list(L, L1, L11),
	delete_list(L11, L2, L22),
	appendAll([F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, L22], OF),
	circle_false(OF, OF1),
	fact_circle(OF1, OF2),
	sort(OF2, F).

delete_list([], _, []) :- !.
delete_list(L, [], L) :- !.
delete_list(L1, [X|L2], L) :- delete(L1, X, L3), delete_list(L3, L2, L).

circle_false([], []) :- !.
circle_false([C|OF], [C1|NF]) :- resolutionKBF(C, C1), circle_false(OF, NF).

appendAll([], []) :- !.
appendAll([X], X) :- !.
appendAll([X,Y|L1], NewL) :- append(X, Y, R), appendAll(L1, L), append(R, L, NewL).

forget([], _, P, []) :- !. %classical rule
forget(_, [], _, []) :- !.
forget([X|L1], L2, P, F) :- forget_list(X, L2, P, F1), forget(L1, L2, P, F2), append(F1, F2, F).

forget_list(X, [], P, []) :- !.
forget_list(X, [Y|L1], P, [H|L2]) :- resolution(X, Y, P, H), forget_list(X, L1, P, L2), !.

forgetKB([], _, P, []) :- !.  % rule-KB and rule-KK
forgetkB(_, [], _, []) :- !.
forgetKB([X|L1], L2, P, F) :- forgetKB_list(X, L2, P, F1), forgetKB(L1, L2, P, F2), append(F1, F2, F).

forgetKB_list(X, [], P, []) :- !.
forgetKB_list(X, [Y|L1], P, L) :- resolutionKB_circle(X, Y, P, H), 
	forgetKB_list(X, L1, P, L2), append(H, L2,L),!.

forgetK([], _, P, []) :- !.  % rule-K
forgetK(_, [], _, []) :- !.
forgetK([X|L1], L2, P, F) :- forgetK_list(X, L2, P, F1), forgetK(L1, L2, P, F2), append(F1, F2, F).

forgetK_list(X, [], P, []) :- !.
forgetK_list(X, [Y|L1], P, L) :- resolutionK(X, Y, P, H), 
	forgetK_list(X, L1, P, L2), append(H, L2,L),!.

forgetKK([], _, P, []) :- !.  % rule-KK
forgetkK(_, [], _, []) :- !.
forgetKK([X|L1], L2, P, F) :- forgetKK_list(X, L2, P, F1), forgetKK(L1, L2, P, F2), append(F1, F2, F).

forgetKK_list(X, [], P, []) :- !.
forgetKK_list(X, [Y|L1], P, L) :- resolutionKK_circle(X, Y, P, H), 
	forgetKK_list(X, L1, P, L2), append(H, L2,L),!.

forgetB([], P, []) :- !.  % rule-B
forgetB([X|L1],P, F) :- resolutionB(X, P, F1), forgetB(L1, P, F2), append(F1, F2, F).

%forgetB_list(X, P, L) :- resolutionB(X, P, H), 
%	forgetB_list(X, L1, P, L2), append(H, L2,L),!.

%-----------------------------end----------------------------------------------


%---------------------------------resolution------------------------
%classical rule
resolution(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1),   
	C2 = kclause(Cclause2, KT2, BT2), 
	Cclause1 = [Cclause11], Cclause2 = [Cclause21], unionC(Cclause11, Cclause21, P, X), 
	append(KT1, KT2, KT), append(BT1, BT2, BT),
	R = kclause([X], KT, BT).

unionC(C1, C2, P, X) :- equall(P, F1), delete(C1, F1, X1), equall(-P, F2), delete(C2, F2, X2), append(X1, X2, X).


%---------------------
%rule KB
resolutionKB(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2), 
	(find_p_resolve(KT1, BT2, P, KX, BX, NewB), (append(KX, KT2, KT), append([NewB], BX, InterB), append(InterB, BT1, BT)) ; 
	find_p_resolve(KT2, BT1, -P, KX, BX, NewB), (append(KX, KT1, KT), append([NewB], BX, InterB), append(InterB, BT2, BT))),
	append(Cclause1, Cclause2, Cclause),
	R = kclause(Cclause, KT, BT).
	
find_p_resolve(KT, BT, P, K, B, R) :- equall(P, F), findPTerm(KT, F, X), equall(-P, F1), findPTerm(BT, F1, Y), 
	delete(KT, X, K), delete(BT, Y, B),
	X = [X1], Y = [Y1],
	unionC(X1, Y1, F, R1),
	append([R1], Y, R).
---------------------

/*equall(-(-P), P) :- prop(P).
equall(-P, -P) :- prop(P).
equall(P, P) :- prop(P).*/




findPTerm([], _, _) :- fail.
findPTerm([Y|KT], P, H) :- equall(P, F), (findPTerm_list(Y, Y, F, X), (H = X, !); findPTerm(KT, P, H)).

findPTerm_list([], _, _, _) :- fail.
findPTerm_list([X|L], O, P, Y) :- equall(P, F), (member(F, X), Y = O; findPTerm_list(L, O, P, Y)).


%the rule-KB
/*resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	((refind_p_resolve(KT1, BT2, P, L, KT1, BT2), L \= []), (reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L, R), write(L)); 
	(refind_p_resolve(KT2, BT1, -P, L, KT2, BT1), L \= []), (reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L, R), write(L))).*/

 /*resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	((refind_p_resolve(KT1, KT1, BT2, P, L), L \= []), reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L, R); 
	(refind_p_resolve(KT2, KT2, BT1, -P, L), L \= []), reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L, R)).*/

resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	refind_p_resolve(KT1, KT1, BT2, P, L), L \= [],
	reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L, R), !.

resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),  
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	refind_p_resolve(KT2, KT2, BT1, -P, L), L \= [],
	reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L, R), !.

%the rule-KK
/*resolutionKB_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	append(BT1, BT2, BT),
	refind_p_resolveKK(KT1, KT1, KT2, P, L), L \= [], reunionKK(Cclause, BT, L, R).*/

resolutionKB_circle(_,_,_,[]) :- !.

%the rule-KK for forgetKK
resolutionKK_circle(C1, C2, P, R) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(Cclause11, Cclause21, Cclause3),
	Cclause = [Cclause3],
	append(BT1, BT2, BT),
	refind_p_resolveKK(KT1, KT1, KT2, P, L), L \= [], reunionKK(Cclause, BT, L, R), !.
resolutionKK_circle(_,_,_,[]) :- !.

%the rule-K
resolutionK(C1, C2, P, H) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(BT1, BT2, BT), 
	equall(P, F),
	(member(F, Cclause11), 
	(resolutionK_list(Cclause11, KT2, KT2, F, L), L \= [], reunionK(Cclause21, KT1, BT, F, L, H));
	member(F, Cclause21), resolutionK_list(Cclause21, KT1, KT1, F, L), L \= [], reunionK(Cclause11, KT2, BT, F, L, H)).
resolutionK(C1, C2, P, H) :- C1 = kclause(Cclause1, KT1, BT1), C2 = kclause(Cclause2, KT2, BT2),
	Cclause1 = [Cclause11], Cclause2 = [Cclause21],
	append(BT1, BT2, BT),
	equall(-P, F),
	(member(F, Cclause11),
	(resolutionK_list(Cclause11, KT2, KT2, F, L), L \= [], reunionK(Cclause21, KT1, BT, F, L, H));
	member(F, Cclause21), resolutionK_list(Cclause21, KT1, KT1, F, L), L \= [], reunionK(Cclause11, KT2, BT, F, L, H)).
resolutionK(_, _, _, []) :- !.  %if the "Kterm" does not contain complementary trem of atom P.


%the rule-B
resolutionB(C, P, NewCL) :- C = kclause(Cclause, KT, BT), 
	resolutionB_list(BT, BT, P, L), unionB(Cclause, KT, L, NewCL).
resolutionB(C, P, C) :- !.

%fact: eliminate the repeat atom and complementary term
fact(C, C1) :- C = kclause(Cclause, KT, BT), 
	factK(KT, KT1),
	factB(BT, BT1),
	(Cclause \= [], (Cclause = [Cclause1], 
	factC(Cclause1, Cclause11),
	C1 = kclause([Cclause11], KT1, BT1));
	C1 = kclause(Cclause, KT1, BT1)).

factC(Cclause, NewC) :-  sort(Cclause, C1), complementary(C1, NewC), !.

%simplify all the KT, eliminate the repeat Kterm
%factK(KT, NewK) :- factK_list(KT, KT2), delete(KT2, [[]], KT1), sort(KT1, NewK).
factK(KT, NewK) :- factK_list(KT, KT1), sort(KT1, NewK), !.

%simplify all the BT, eliminate the repeat Bterm
%factB(BT, NewB) :- factB_list(BT, BT2), delete(BT2, [[]], BT1), sort(BT1, NewB).
factB(BT, NewB) :- factB_list(BT, BT1), sort(BT1, NewB), !.

%simplify Kterm, eliminate the repeat atoms in Kterm
factK_list([], []) :- !.
factK_list([X|L1], [Y|L2]) :- X = [X1], factC(X1, X11), Y = [X11], factK_list(L1, L2).

%simplify Bterm, eliminate the repeat atoms in Bterm
factB_list([], []) :- !.
factB_list([X|L1], [Y|L2]) :- factB_list_one(X, N1), delete(N1, [], N), sort(N, Y), factB_list(L1, L2).

%eliminate the repeat atoms in subterm of Bterm
factB_list_one([], []) :- !.
factB_list_one([X|L1], [Y|L2]) :- factC(X, Y), factB_list_one(L1, L2).


complementary(C, []) :- member(P, C), member(-P, C), !.
complementary(C, C) :- !.


%the rule-KBF: eliminate the term which is false
resolutionKBF(C, C1) :- C = kclause(Cclause, KT, BT), 
	find_falseSolvK(KT, NKT),
	find_falseSolvB(BT, NBT),
	C1 = kclause(Cclause, NKT, NBT).

find_falseSolvK([], []) :- !. 
find_falseSolvK([X|KT], [X|L]) :- \+ ([] == X),  find_falseSolvK(KT, L).  
find_falseSolvK([X|KT], L) :- [] == X,  find_falseSolvK(KT, L).  %if [] == X, then X is false

find_falseSolvB([], []) :- !.
find_falseSolvB([X|KT], [X|L]) :- \+ member([], X),  find_falseSolvB(KT, L).
find_falseSolvB([X|KT], L) :- member([], X),  find_falseSolvB(KT, L). %if member([], X), then X is false


reunionKK(Cclause, _, [], []) :- !.
reunionKK(Cclause, BT, [X|L1], [R|L2]) :- X = [K1, K2, NewK], 
	append(K1, K2, KTT),
	append([NewK], KTT, KT),
	R = kclause(Cclause, KT, BT),
	reunionKK(Cclause, BT, L1, L2).

reunionKB_pos(_, _, _, _, _, [], []) :- !.	
reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, [R|L1], [C|L2]) :- R = [KX, BX, NewB], 
	append(KX, KT2, KT), append([NewB], BX, InterB), append(InterB, BT1, BT), 
	C = kclause(Cclause, KT, BT),
	reunionKB_pos(Cclause, KT1, BT2, KT2, BT1, L1, L2).

reunionKB_neg(_, _, _, _, _, [], []) :- !.
reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, [R|L1], [C|L2]) :- R = [KX, BX, NewB], 
	append(KX, KT1, KT), append([NewB], BX, InterB), append(InterB, BT2, BT),
	C = kclause(Cclause, KT, BT),
	reunionKB_neg(Cclause, KT2, BT1, KT1, BT2, L1, L2).

reunionK(_, _, _, _, [], []) :- !. 
reunionK(Cclause, KT1, BT, P, [X|L], [C|H]) :-  X = [K1, NewC1],
	append(K1, KT1, KT),
	unionC(NewC1, Cclause, P, NewC),
	C = kclause([NewC], KT, BT),
	reunionK(Cclause, KT1, BT, P,L, H).

unionB(_, _, [], []) :- !.
unionB(Cclause, KT, [X|L], [NewC|L2]) :-  NewC = kclause(Cclause, KT, X), 
	unionB(Cclause, KT, L, L2).
%-----------------------------------------------------------------------------------

%find the Kterm which contain p and Bterm which contain -P, then compute all the possible resolution and return the consquences.
% e.g: given KT = [[[c, -b]]],  BT= [[[b,a]], [[c,b]]], 
% then the result by resolution "b" is [[[], [[[c, b]]], [[c, a], [b, a]]], [[], [[[b, a]]], [[c, c], [c, b]]]]
/*refind_p_resolve(KT, BT, P, [], [], _).
refind_p_resolve(KT, BT, P, [], _, []).
refind_p_resolve(KT, BT, P, L, K1, B1) :- equall(P, F), findPTerm(K1, F, X), equall(-P, F1), findPTerm(B1, F1, Y), 
	delete(K1, X, K), delete(B1, Y, B), 
	resolveK(KT, BT, X, Y, P, R),
	refind_p_resolve(KT, BT, P, L1, KT, B),
	refind_p_resolve(KT, BT, P, L2, K, BT),
	append(R, L1, L3),
	append(L3, L2, L).
refind_p_resolve(KT, BT, P, [], K1, B1) :- equall(P, F), \+ findPTerm(K1, F, X).
refind_p_resolve(KT, BT, P, [], K1, B1) :- equall(-P, F1), \+ findPTerm(B1, F1, Y).*/

refind_p_resolve([], KT, BT, P, []) :- !.
refind_p_resolve(KT1, KT, [], P, []) :- !.
refind_p_resolve([X|L1], KT, BT, P, L) :-  refindPResListKB(X, KT, BT, BT, P, R),
	refind_p_resolve(L1, KT, BT, P, L2),
	append(R, L2, L).

refindPResListKB(_, _, _, [], _, []) :- !.
refindPResListKB(K, KT, BT, NewB, P, []) :- equall(P, F), K = [K1], \+ member(F, K1), !.
refindPResListKB(K, KT, BT, NewB, P, []) :- equall(-P, F1), \+ findPTerm(NewB, F1, Y), !.
refindPResListKB(K, KT, BT, NewB, P, L) :- equall(P, F), K = [K1], member(F, K1), 
	equall(-P, F1), !, findPTerm(NewB, F1, Y), !,
	delete(NewB, Y, NewB1),
	resolveK(KT, BT, K, Y, P, R), !,
	refindPResListKB(K, KT, BT, NewB1, P, L1),
	append(R, L1, L).

/*resolveK(KT, BT, X, Y, P, R) :- delete(KT, X, K), delete(BT, Y, B),
	equall(P, F),
	X = [X1], Y = [Y1],
	unionC(X1, Y1, F, R1),
	append([R1], Y, R2),
	R = [K, B, R2].*/

%compute all the resolution between a Kterm X(which contain P or -P) and subterm Y(which contain -P or P) in a Bterm
resolveK(KT, BT, X, Y, P, R) :- delete(KT, X, K), delete(BT, Y, B),
	equall(P, F),
	unionKB(X, Y, F, L), %write(L), nl,
	append_list(L, K, B, Y, R).
	
unionKB(K, [], _, []).
unionKB(K, [B|L1], P, [R|L2]) :- equall(-P, F), K = [X1], member(F, B), unionC(X1, B, P, R), unionKB(K, L1, P, L2).
unionKB(K, [B|L1], P, L2) :- equall(-P, F), K = [X1], \+ member(F, B), unionKB(K, L1, P, L2).

append_list([], _, _, _, []).
append_list([X|L1], K, B, Y, [R|L2]) :-  append([X], Y, R1), R = [K, B, R1], append_list(L1, K, B, Y, L2).



refind_p_resolveKK([], KT1, KT2, P, []) :- !.
refind_p_resolveKK(KT1, KT1, [], P, []) :- !.
refind_p_resolveKK([X|L1], KT1, KT2, P, L) :-  refindPResList(X, KT1, KT2, KT2, P, R),
	refind_p_resolveKK(L1, KT1, KT2, P, L2),
	append(R, L2, L).

refindPResList(_, _, _, [], _, []) :- !.
refindPResList(K, KT1, KT2, NewK, P, []) :- equall(P, F), K = [K1], \+ member(F, K1), !.
refindPResList(K, KT1, KT2, NewK, P, []) :- equall(-P, F1), \+ findPTerm(NewK, F1, Y), !.
refindPResList(K, KT1, KT2, NewK, P, [R|L]) :- equall(P, F), K = [K1], member(F, K1), 
	equall(-P, F1), !, findPTerm(NewK, F1, Y), !,
	delete(NewK, Y, NewK1),
	resolveKK(KT1, KT2, K, Y, P, R), !,
	refindPResList(K, KT1, KT2, NewK1, P, L).


resolveKK(KT1, KT2, X, Y, P, R) :- delete(KT1, X, K1), delete(KT2, Y, K2),
	X = [X1], Y = [Y1],
	unionC(X1, Y1, P, NewK),
	R = [K1, K2, [NewK]].


resolutionK_list(Cclause, KT, [], P, []) :- !.
resolutionK_list(Cclause, KT, NewK, P, []) :- equall(-P, F), \+ findPTerm(NewK, F, Y), !.
resolutionK_list(Cclause, KT, NewK, P, [R|L]) :- equall(-P, F), findPTerm(NewK, F, Y), 
	delete(NewK, Y, NewK1), delete(KT, Y, K1),
	Y = [Y1],
	unionC(Cclause, Y1, P, NewC),
	R = [K1, NewC],
	resolutionK_list(Cclause, KT, NewK1, P, L).

resolutionB_list(_, [], _, []) :- !.
resolutionB_list(BT, [X|L1], P, L) :- resolutionB_list_one(BT, X, P, L2), 
	resolutionB_list(BT, L1, P, L3),
	append(L2, L3, L).
	

gainNewBT(_, _, [], []) :- !.
gainNewBT(BT, X, [Y|L], [NewBT|L1]) :- delete(BT, X, BT1),  
	append([Y], X, B), append([B], BT1, NewBT),
	gainNewBT(BT, X, L, L1).

resolutionB_list_one(_, [], _, []) :- !.
resolutionB_list_one( BT, L, P, L1) :- splitINP(L, P, LP, LN),
	resolB(LP, LN, P, L2), 
	gainNewBT(BT, L, L2, L1).

%gain all the possible NewB
resolB([], _, _, []) :- !.
resolB(_, [], _, []) :- !.
resolB([X|LP], LN, P, L) :- resolB_list(X, LN, P, L1), resolB(LP, LN, P, L2), append(L1, L2, L).

resolB_list(X, [], _, []) :- !.
resolB_list(X, [Y|L1], P, [NewC| L2]) :- unionC(X, Y, P, NewC), resolB_list(X, L1, P, L2).

%split L to two list L1 and L2
%L1: contain P
%L2: contain -P
splitINP([], _, [], []) :- !.
splitINP([X|L], P, [X|LP], LN) :- member(P, X), splitINP(L, P, LP, LN).
splitINP([X|L], P, LP, [X|LN]) :- member(-P, X), splitINP(L, P, LP, LN).
splitINP([X|L], P, LP, LN) :- splitINP(L, P, LP, LN).



%----------------------------------end-----------------------------


%-----------------------split_p/6--------------------------------------------
%split the set of KClause to six lists, which is L1, L2, L3, L4,L5, L6
%L1: the set of KClause-kclause(L1, L2, L3), where P is a member of L1
%L2: the set of KClause-kclause(L1, L2, L3), where -P is a member of L1
%L3: the set of KClause-kclause(L1, L2, L3), where P is a member of L2 or L3
%L4: the set of KClause-kclause(L1, L2, L3), where -P is a member of L2 or L3
%L5: the set of KClause-kclause(L1, L2, L3), where -P and P is a member of L2 or L3
%L6: the others
split_p([],_,[],[],[],[], [], []) :- !.
split_p([X|L], P, [X|L1], L2, L3, L4, L5, L6) :- X = kclause(Cclause, KT, BT), 
	Cclause \= [], Cclause = [Cclause1], member(P, Cclause1), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, [X|L2], L3, L4, L5, L6) :- X = kclause(Cclause, KT, BT), 
	Cclause \= [], Cclause = [Cclause1], member(-P, Cclause1), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, -P), member_b(BT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), member_k(KT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, L4, [X|L5], L6) :- X = kclause(Cclause, KT, BT), member_b(KT, P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, [X|L3], L4, L5, L6) :- X = kclause(Cclause, KT, BT), member_k(KT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, [X|L3], L4, L5, L6) :- X = kclause(Cclause, KT, BT), \+ member_k(KT, P), member_b(BT, P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, [X|L4], L5, L6) :- X = kclause(Cclause, KT, BT), member_k(KT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.
split_p([X|L], P, L1, L2, L3, [X|L4], L5, L6) :- X = kclause(Cclause, KT, BT), \+ member_k(KT, -P), member_b(BT, -P), 
	split_p(L, P, L1, L2, L3, L4, L5, L6), !.

split_p([X|L], P, L1, L2, L3, L4, L5, [X|L6]) :- split_p(L, P, L1, L2, L3, L4, L5, L6).


%if P appear in KT then return true, else false.
member_k(KT, P) :- member_klist(KT, P).

member_klist([], P) :- fail.
member_klist([X|L], P) :- X = [Y], (member(P, Y), !; member_klist(L, P)).

%if P appear in BT then return true, else false.
member_b(KT, P) :- member_blist(KT, P).

member_blist([], P) :- fail.
member_blist([X|L], P) :- (member_list(X, P), !; member_blist(L, P)).

member_list([], P) :- fail.
member_list([X|L], P) :- (member(P, X), !; member_list(L, P)).

%----------------mcnf2list--------------------------------------------------------

mcnf2Lst(F, [KC|L]) :- F =.. [Y|Args], (Y == &), !, Args = [X, M], kc2list(M, KC), mcnf2list(X, L), !.

mcnf2list(F, [KC|L]) :- F =.. [Y|Args], (Y == &), !, Args = [X, M], kc2list(X, KC), mcnf2list(M, L), !.
mcnf2list(F, [C]) :- kc2list(F, C).

kc2list(KC, kclause(Cclause, KT, BT)) :- devive(KC, L1, L2, L3), 
	(L3 \= [], Cclause=[L3]; Cclause = L3), 
	kterm2list(L1, KT), bterm2list(L2, BT), cons_delet.

%----------------end-----------------------------------------------------------


%--------------------------kterm2list---and---bterm2list---------
kterm2list([], []).
kterm2list([X|L], [H|L1]) :- pair(F, X), F = @P, wff2cnf(P, H), kterm2list(L, L1).

bterm2list([],[]).
bterm2list([X|L], [H|L1]) :- pair(F, X), F = $P, wff2cnf(P, H), bterm2list(L, L1).

%-----------------------------end---------------------------------------------------


devive(C, L1, L2, L3) :- kbc_len(C, Klen, Blen, 0, 0) ,   generate_KBterm(Klen, Blen) ,  
	Klen > 0, Blen > 0 ,
	new_substitute_allk(C, C1,1) , new_substitute_allb(C1, C2,1) ,
	wff2cnf(C2, CNF) , 
	%write("CNF="), write(CNF), nl,
	%simply_dnf(DNF, F1),
	%write("DNF_simple="), write(F1), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).

devive(C, L1, L2, L3) :- kbc_len(C, Klen, Blen, 0, 0) ,   generate_KBterm(Klen, Blen) ,  
	Klen = 0, Blen = 0 ,
	%new_substitute_allk(C, C1,1) , new_substitute_allb(C1, C2,1) ,
	wff2cnf(C, CNF) , 
	%write("CNF="), write(CNF), nl,
	%simply_dnf(DNF, F1),
	%write("DNF_simple="), write(F1), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).

	
devive(C, L1, L2, L3) :- klist(KL), write("KL="), write(KL), nl, blist(BL), write("BL="), write(BL), nl, 
	  kbc_len(C, Klen, Blen, 0, 0) ,   Klen == 0, Blen > 0,   
	generate_KBterm(Klen, Blen) ,
	%generate_list(1, Blen, L2) ,
	%change2Bterm(L2, BL) ,
	%assert(blist(BL)) ,
	new_substitute_allb(C, C2,1) ,
	wff2cnf(C2, CNF) ,
	%write("CNF="), write(CNF), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).
	
devive(C, L1, L2, L3) :- klist(KL), %write("KL="), write(KL), nl, 
	blist(BL), write("BL="), write(BL), nl,
	kbc_len(C, Klen, Blen, 0, 0),   Blen == 0, Klen > 0 ,
	generate_KBterm(Klen, Blen) ,
	%generate_list(1, Klen, L2) ,   
	%change2Kterm(L2, KL) ,
	%assert(klist(KL)) ,
	new_substitute_allk(C, C2,1) ,
	wff2cnf(C2, CNF) ,
	%write("CNF="), write(CNF), nl,
	CNF = [Clause],
	split_k(Clause, L1, L2, L3).




%-------------new_substitute_allk-----new_substitute_allb----------------
%Substitute terms @P in Formula with new atoms
new_substitute_allk(Term, NewTerm, N1) :-   getTermk(Term1,N1,L),
	  substitute(@P,Term, Term1, F, Flag),  
	assert(pair(@P,Term1)),
	assert(prop(Term1)),
	(Flag==true, N2 is N1+1; N2 is N1),
	(F == Term, NewTerm = F; new_substitute_allk(F, NewTerm, N2)).

new_substitute_allb(Term, NewTerm, N1) :-   getTermb(Term1,N1,L),  
	substitute($P,Term, Term1, F, Flag),  
	assert(pair($P,Term1)),
	assert(prop(Term1)),
	(Flag==true, N2 is N1+1; N2 is N1),
	(F == Term, NewTerm = F; new_substitute_allb(F, NewTerm, N2)).

% gain a new atom from klist(which is generate dynamic) to substitute
% term @P
getTermk(Term1, N,L) :- %L= [k1,k2,k3,k4,k5,k6,k7,k8,k9,k10,k11],
	klist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%gain a new atom from blist to substitute term $P
getTermb(Term1, N,L) :- %L=[b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11],
	blist(L), length(L, N1), (N1 < N, Term1='a'; th_list(L,N,Term1)).

%substitute @P or $P in formula with new atom
substitute(Term, Term, Terml, Terml, Flag) :- Flag=true,
	%write("Flag''="),write(Flag), nl,
	!.
substitute( _, Term, _, Term, Flag) :- atomic( Term), Flag=false, !.
substitute( Sub, Term, Subl, Terml, Flag) :- Term =.. [F | Args], substlist(Sub, Args, Subl, Argsl, Flag), Terml =.. [F | Argsl].

substlist(_, [],_,[], Flag) :- Flag=false.
substlist(Sub, [Term | Terms], Subl, [Terml | Termsl], Flag):- substitute(Sub, Term, Subl, Terml, Flag1),
		substlist( Sub, Terms, Subl, Termsl, Flag2),
		(Flag1=true, Flag=Flag1; Flag=Flag2).

list_th([H|T],X, N,H) :- N == X,!.
list_th([H|T],X, N,Y) :- M is N+1, list_th(T,X, M,Y).
list_th(F,X, N,Y):- X =< 0, write("error: N<=0").
%list_th(F,X, N,Y):- length(F,L), X > L+1, write("error: N > length of list"), nl, write(N), nl.

th_list(F,X,Y):- list_th(F,X,1,Y).

% ----------end new_substitute_allk-----new_substitute_allb-------------


%----------wff2cnf------and--------wff2dnf--------
wff2cnf(P, [[P]]) :- prop(P), !.
wff2cnf(-P, [[-P]]) :- prop(P), !.
wff2cnf(P->Q, L) :- wff2cnf(-P\/Q, L), !.%/
wff2cnf(P<->Q, L) :- wff2cnf((-P\/Q)&(-Q\/P), L), !.%/
wff2cnf(P&Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), append(L1,L2,L), !.
wff2cnf(P\/Q, L) :- wff2cnf(P,L1), wff2cnf(Q,L2), %/
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L), !.
wff2cnf(-P, L) :- wff2dnf(P, L1), negate(L1, L), !.

/* wff2cnf(W,NewW) :- negation_inside(W,W1), wff2cnf0(W1,NewW).
*/
wff2cnf0(P, [[P]]) :- prop(P), !.
wff2cnf0(-P, [[-P]]) :- prop(P), !.
wff2cnf0(P&Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), union(L1,L2,L), !.
wff2cnf0(P\/Q, L) :- wff2cnf0(P,L1), wff2cnf0(Q,L2), %/
    setof(X, Y^Z^(member(Y,L1), member(Z,L2), union(Y,Z,X)), L), !.
	

	/* wff2dnf transforms a wff to its disjunctive normal form in list format */

wff2dnf(P,[[P]]) :- prop(P), !.
wff2dnf(-P,[[-P]]) :- prop(P), !.
wff2dnf(P->Q, L) :- wff2dnf(-P\/Q, L).
wff2dnf(P<->Q, L) :- wff2dnf((P->Q)&(Q->P), L).
wff2dnf(P\/Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2), append(L1,L2,L).
wff2dnf(P&Q, L) :- wff2dnf(P,L1), wff2dnf(Q,L2),
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L).
wff2dnf(-P, L) :- wff2cnf(P,L1), negate(L1,L).
%----------------end----------------------------------------------

%---------------new_wff2dnf-------new_wff2cnf----------------------------------
%excludeing the repetitive term (or clause)

%the union, which have no repetitive element, of two sets 
nonRep(L1, L2, L) :- findall(X, (member(X, L1), member(X, L2)), L11),
	difference_list(L11, L2, L22),
	difference_list(L11, L1, L33),
	append(L11, L22, L3),
	append(L3, L33, L).
	
/* Wff2dnf transforms a wff to its disjunctive normal form in list format */
new_wff2dnf(P,[[P]]) :- prop(P), !.
new_wff2dnf(-P,[[-P]]) :- prop(P), !.
%new_wff2dnf(P->Q, L) :- new_wff2dnf(-P\/Q, L). 
%new_wff2dnf(P<->Q, L) :- new_wff2dnf((P->Q)&(Q->P), L). %/
new_wff2dnf(P\/Q, L) :- new_wff2dnf(P,L1), new_wff2dnf(Q,L2), nonRep(L1,L2,L). %/
%new_wff2dnf(P&Q, L) :- new_wff2dnf(P,L1), new_wff2dnf(Q,L2),
%    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L).
new_wff2dnf(-P, L) :- new_wff2cnf(P,L1), negate(L1,L).

/* negate(L1,L): negate L1 in DNF (CNF) and make it into a CNF (DNF). */
negate([],[]) :- !.
negate([[]],[[]]) :- !.
negate(L1,L) :- bagof(X, Y^(member(Y, L1), negate_one_clause(Y,X)), L).

/* negate_one_clause(L1, L2): make all elements in L1 into its complement */
negate_one_clause(L1, L2) :- bagof(X, Y^(member(Y,L1), complement(Y,X)), L2).

complement(true,false) :- !.
complement(false,true) :- !.
complement(P,-P) :- prop(P).
complement(-P,P) :- prop(P).

/* Wff2cnf transforms a wff to its conjunctive normal form in list format */
new_wff2cnf(P, [[P]]) :- prop(P), !.
new_wff2cnf(-P, [[-P]]) :- prop(P), !.
%new_wff2cnf(P->Q, L) :- new_wff2cnf(-P\/Q, L), !.  
%new_wff2cnf(P<->Q, L) :- new_wff2cnf((-P\/Q)&(-Q\/P), L), !.  
%new_wff2cnf(P&Q, L) :- new_wff2cnf(P,L1), new_wff2cnf(Q,L2), nonRep(L1,L2,L), !.%/
new_wff2cnf(P\/Q, L) :- new_wff2cnf(P,L1), new_wff2cnf(Q,L2),  %/
    findall(X, (member(Y,L1), member(Z,L2), append(Y,Z,X)), L), !.
new_wff2cnf(-P, L) :- new_wff2dnf(P, L1), negate(L1, L), !.


%L = L2 - L1 and L2 >= L1(must be true)
difference_list([],L2, L2) :- !.
difference_list(L1, L2, L) :-  bagof( X, (member(X, L2), \+ member(X, L1)), L), !.

%------------end new_wff2dnf-------new_wff2cnf--------------------------------


%----------------simplify the dnf-------------


simply_dnf(DNF, NEWDNF) :- sort_list(DNF, DNF1),
%	dnf_init_minimize(DNF1,[], NEWDNF),
	!, dnf_simplifies(DNF1, NEWDNF).

sort_list([], []) :- !.
sort_list([D|DNF], [NewD|NewDNF]) :-
	sort(D, NewD),
	sort_list(DNF, NewDNF).



/*dnf_init_minimize(DNF1, DNF2, NewDNF) :- member(D, DNF1),
	difference(DNF1, D, DNF3), union(DNF3, DNF2, DNF4),
	dnf_simplifies(DNF4, DNF5), member(D1, DNF5), dnf_subsumes(D1, D), !,
	dnf_init_minimize(DNF3, DNF2, NewDNF).
dnf_init_minimize(DNF, [], NewDNF):- dnf_simplifies(DNF, NewDNF).*/

/* cnf_simplifies(L,NewL): simplifies DNF L into L1 by eliminating repetitive
   literals and contradictive literals. It also eliminates clauses that
   subsumes others.
DNFCNF L L1L
*/


dnf_simplifies(DNF, NewDNF) :- dnf_sort_simpl(DNF, DNF1),
	dnf_unit_elim(DNF1, DNF2),
	dnf_sort_simpl(DNF2, DNF3),
	check_tauto(DNF3, DNF4),
	dnf_minimize(DNF4, NewDNF).

/*dnf_simplifies2(DNF, NewDNF) :- dnf_sort_simpl(DNF, DNF1), %time waster
	dnf_minimize(DNF1, DNF2),
	dnf_unit_elim(DNF2, DNF3),
	dnf_sort_simpl(DNF3, DNF4),
	check_tauto(DNF4, DNF5),
	dnf_minimize(DNF5, NewDNF).*/

/*dnf_simplifies(DNF, NewDNF) :-
	dnf_sort_simpl(DNF, DNF1), %ignorate the negative atom.
	dnf_minimize(DNF1, DNF2),
%	dnf_unit_elim(DNF2, DNF3),
	dnf_sort_simpl(DNF2, DNF3),
	check_tauto(DNF3, DNF4),
	dnf_minimize(DNF4, NewDNF).*/




%sort(List, NL):  Duplicates in List are removed.

/* sort each clause and get rid of contradictory */
dnf_sort_simpl([], []).
dnf_sort_simpl(DNF, [[]]) :- member([], DNF), !.
dnf_sort_simpl(DNF, [[]]) :- member([true], DNF), !.
dnf_sort_simpl(DNF, [[]]) :- member([-false], DNF), !.
dnf_sort_simpl([C|DNF], NewDNF) :- member(false, C), !,
	dnf_sort_simpl(DNF, NewDNF).
dnf_sort_simpl([C|DNF], NewDNF) :- member(-P, C), member(P, C), !,
	dnf_sort_simpl(DNF, NewDNF).
dnf_sort_simpl([C|DNF], NewDNF) :-
	sort(C, NewD1), subtract(NewD1, [-false, true], NewD),
        ((NewD=[],NewDNF=[[]]);
	 (dnf_sort_simpl(DNF, NewDNF1), NewDNF=[NewD|NewDNF1])),!.


/* eliminates all unit clauses */
dnf_unit_elim(DNF, [[P]|NewDNF]) :-
	member([P], DNF),
	dresolve(DNF, P, DNF2), !,
	dnf_unit_elim(DNF2, NewDNF), !.
dnf_unit_elim(DNF, DNF) :- !.



dresolve([],_,[]).
dresolve([D|DNF], P, NewDNF) :- member(P, D), !,
%	difference(D, P, NewD),
	dresolve(DNF, P, NewDNF).
dresolve([D|DNF], P, [NewD|NewDNF]) :- complement(P, P1),
	difference(D, P1, NewD),
	dresolve(DNF, P, NewDNF).

%check for tautologies
check_tauto(DNF, [[]]) :- member([], DNF), !.
check_tauto(DNF, DNF).


dnf_minimize(DNF, DNF1) :- member(L, DNF), member(L1, DNF), L\==L1,
	dnf_subsumes(L, L1), difference(DNF, L1, DNF2),
	dnf_minimize(DNF2, DNF1), !.
dnf_minimize(DNF, DNF).



%subset(L1, L2): if L1 is a subset of L2, then return true, else fales.
dnf_subsumes(L,L1) :- \+ (member(X,L), X\==true, X\==(-false),
    \+ member(X,L1)).

	
	/* difference(L,P,L1): L1 is L - [P] */
difference([P | L], P, L) :- !.
difference([Q | L], P, [Q | NewL]) :- difference(L,P,NewL).
difference([],P,[]).
%-------------------end simplify --------------------------


%------------------------generate K and B term for substitute --------------------------
generate_KBterm(LK, LB) :- generate_list(1, LK, L1),
	change2Kterm(L1, KL),
	generate_list(1, LB, L2),
	change2Bterm(L2, BL),
	assert(klist(KL)),
	assert(blist(BL)).
	
change2Kterm([], []) :- !.
change2Kterm([X|L], [KX|KL]) :- string_concat('k', X, KY),
	string_to_atom(KY, KX),
	change2Kterm(L, KL).


change2Bterm([], []) :- !.
change2Bterm([X|L], [BX|BL]) :- string_concat('b', X, BY),
	string_to_atom(BY, BX),
	change2Bterm(L, BL).

%generate a list L which is between 1 to N.
generate_list(1, N, []) :- N < 1, !.
generate_list(1, 1, [1]) :- !.
generate_list(1, N, [N|L]) :- X is N-1, generate_list(1, X, L), !.

%-------------------------end-----------------------------


%-----------------------------compute the length of K term and B term of a KClause-----------
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == \/ , !, kc_listLen(Args, Klen, Blen, M, N), !. %/
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == @ , !, kc_length(C, Klen, Blen, M, N), !.
kbc_len(C, Klen, Blen, M, N) :- C =.. [Y|Args], Y == $ , !, kc_length(C, Klen, Blen, M, N), !.
kbc_len(C, M, N, M, N) :- !.

kc_listLen([], M, N, M, N) :- !.
kc_listLen([X|L], K, B, M, N) :-   kc_length(X, N1, N2, M, N), L = [Y],   kbc_len(Y, K, B, N1, N2). 

kc_length(C, KLen, BLen, N1, N2) :-  C =.. [Y|Args], Y == @, N11 is N1+1, KLen = N11, BLen = N2.
kc_length(C, KLen, BLen, N1, N2) :-  C =.. [Y|Args], Y == $, N21 is N2+1, KLen = N1, BLen = N21.
kc_length(C, N1, N2, N1, N2) :- !.

%-------------------------end----------------------------------------------

%---------------------split_k-------------------------------
% split the list of term to three classes, L1 is the list of term @P, L2
% is the list of term of $P and L3 is the list of objective term
split_k([],[],[],[]) :- !.
split_k([H|T], [H|L1], L2, L3) :- klist(L),  member(H, L), split_k(T, L1, L2, L3), !.
split_k([H|T], L1, [H|L2], L3) :- blist(L),  member(H, L), split_k(T, L1, L2, L3), !.
split_k([H|T], L1, L2, [H|L3]) :- split_k(T, L1, L2, L3), !.

%---------------------end split_k----------------------------------



%-------------------kcnf2Kwff----------------------------------
kcnf2Kwff(Kcnf, Kwff) :- kcnf2Kwff_list(Kcnf, F), union2Kwff(F, Kwff).

kcnf2Kwff_list([], []).
kcnf2Kwff_list([C|L1], [W|L2]) :- C = kclause(Clause, Kterm, Bterm),
	(a(Clause) = a([]), Wff = false; cnf2wff(Clause, Wff)),
	kterm2wff(Kterm, KL),
	bterm2wff(Bterm, BL),
	union2KClause(Wff, KL, BL, W),
	kcnf2Kwff_list(L1, L2).

union2Kwff([], true) :- !.
union2Kwff([X], X) :- !.
union2Kwff([X, Y |L], F) :- F1 = (X & Y), union2Kwff(L, F2), F = (F1 & F2).

kterm2wff([], false) :-!.
kterm2wff([[]], true) :- !.
kterm2wff([L], @W) :- cnf2wff(L, W), !.
kterm2wff([K1|L1], @W1 \/ W2 ):- cnf2wff(K1, W1), kterm2wff(L1, W2).
	
bterm2wff([], false) :- !.
bterm2wff([[]], true) :- !.
bterm2wff([L], $W) :- cnf2wff(L, W), !.
bterm2wff([K1|L1], $W1 \/ W2 ):- cnf2wff(K1, W1), bterm2wff(L1, W2).

union2KClause(true, _, _, true) :- !.
union2KClause(_, true, _, true) :- !.
union2KClause(_, _, true, true) :- !.
union2KClause(false, KL, BL, W) :- union2KClausell(KL, BL, W).
union2KClause(Wff, KL, BL, W) :- union2KClausff(Wff, KL, BL, W).

union2KClausell(false, BL, BL) :- !.
union2KClausell( KL, false, KL) :- !.
union2KClausell(KL, BL, KL \/ BL) :- !.

union2KClausff(Wff, false, false, Wff) :- !.
union2KClausff(Wff, false, BL, Wff \/ BL) :- !.
union2KClausff(Wff, KL, false, Wff \/ KL) :- !.
union2KClausff(Wff, KL, BL, Wff \/ BL \/ KL) :- !.

%---------------cnf2wff----dnf2wff-----------
/* dnf2wff(L,W) convert a DNF list to a formula */

dnf2wff([],false) :- !.
dnf2wff([[]],true) :- !.
dnf2wff([L], W) :- list2conjunct(L,W), !.
dnf2wff([L1|L2], W1 \/ W2) :- list2conjunct(L1, W1), dnf2wff(L2,W2).

/* cnf2wff(L,W) convert a CNF list to a formula */

cnf2wff([[]],false) :- !.
cnf2wff([],true) :- !.
cnf2wff([L], W) :- list2disjunct(L,W), !.
cnf2wff([L1|L2], W1 & W2) :- list2disjunct(L1, W1), cnf2wff(L2,W2).


/* list2conjunct(L,A): A is the conjunction of all formulas in L */

list2conjunct([P],P) :- !.
list2conjunct([P | L],P & W) :- list2conjunct(L,W).


/* list2disjunct(L,A): A is the disjunction of all formulas in L: A=false when
   L is empty */

list2disjunct(L, true) :- member(true,L), !.
list2disjunct(L, true) :- member(-P,L), member(P,L), !.
list2disjunct(L, W) :- sort(L,L1), delete(L1,false,L2), list2disj(L2,W), !.
list2disj([], false) :- !.
list2disj([P],P) :- !.
list2disj([P | L],P \/ W) :- list2disj(L,W).

%-----------------------------end--------------------------------------



