-module(utils).
-export([build_update/3,    % evalulation of update, no vars
	 build_msg/4,
	 build_apred/3,     % evaluation of aware pred
	 build_spred/4,
	 build_rpred/5,
	 build_pc_guard/2,
	 build_pc_list/2]).

%% build updates a := E
%% E in the update may be a variable from the message or variable from a previous bound,
build_update(Upd, I, B) ->
    build_update(Upd, I, B, []).

build_update([], _, _, Acc) ->
    string:join(lists:reverse(Acc), ";\n    ");
build_update([H|T], I, B, Acc) ->
    build_update(T, I, B, [evalu(H,I,B) | Acc]).

build_apred(G, I, B) ->
%   io:format("build aware pred ~p with i ~p, b ~p ~n",[Pred,I,B]),
    "(" ++ evala(G, I, B) ++")".

%% this functions returns code for subpredicates if there any (to deal with membership predicate) and code for the input predicate Pred
build_spred(SPred, I, B, OAs) ->
   % io:format("build sending pred ~p ~n",[Pred]),
    "(" ++ evals(SPred, I, B, OAs) ++ ")".
%% receiving predicates can refer to previous variables in Bound or new variables in the message
build_rpred(RPred, I,  B, M, OAs) ->
    " && (" ++ evalr(RPred, I, B, M, OAs) ++ ")".

evalu({self,A}, _, _) ->
    A ++ "[_i]";
evalu({parenthesis,P},I, B) ->
    "(" ++ evalu(P,I, B) ++ ")";
evalu({bracket,E}, I, B) ->
    "[" ++ evalu(E,I, B) ++ "]";
evalu({bracket2,E}, I, B) ->  % set as vector
    "[" ++ evalu(E,I, B) ++ "]";
evalu({selector,List,Index}, I,B) -> evalu(List,I,B) ++ "[" ++ evalu(Index,I,B) ++ "]";
evalu({length, R}, I, B) ->
    evalu(R, I, B) ++ ".length";
evalu("true", _,_) -> "true";
evalu("false", _,_) -> "false";
evalu({const,C}, _,_) -> C;
evalu({minusconst,C}, _,_) -> "-" ++ C;
evalu([H|T] = L,I,B) -> %really bracket of a list
    string:join([evalu(X,I, B) || X <- L],",");
evalu({'+',L,R}, I, B) -> evalu(L,I,B) ++ "+" ++ evalu(R,I,B);
evalu({'-',L,R}, I, B) -> evalu(L,I,B) ++ "-" ++ evalu(R,I,B);
evalu({'*',L,R}, I, B) -> evalu(L,I,B) ++ "*" ++ evalu(R,I,B);
evalu([], _,_) -> [];
evalu({literal, T}, I, B) ->
    %io:format("information before build ~p ~p ~p~n",[T,I,B]),
    case proplists:get_value(T,B) of
	undefined ->
	     T ++ "[_i]";
	_ ->
	    "bound[_i][" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]"
    end;
evalu({token,T}, _,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evalu({concat,L,R}, I, B) ->
    evalu(L,I,B) ++ "+"  ++ evalu(R,I,B);
evalu({assign, L, R}, I,B) ->
    % remeber if this is a set
    Right =  evalu(R, I, B),
    evalu(L, I, B) ++ " = " ++ Right;
evalu({eq, L, R}, I,B) ->
    evalu(L, I, B) ++ " == " ++ evalu(R, I, B);
evalu({diff, L, R}, I, B) ->
    evalu(L, I, B) ++ " != " ++ evalu(R, I, B);
evalu({ge, L, R}, I, B) ->
    evalu(L, I, B) ++ " > " ++ evalu(R, I, B);
evalu({geq, L, R}, I, B) ->
    evalu(L, I, B) ++ " >= " ++ evalu(R, I, B);
evalu({le, L, R}, I, B) ->
    evalu(L, I, B) ++ " < " ++ evalu(R, I, B);
evalu({intersect, L, R}, I, B) ->
    evalu(L, I, B) ++ " && " ++ evalu(R, I,B);
evalu({union, L, R}, I, B) ->
    evalu(L, I, B) ++ " || " ++ evalu(R, I, B);
evalu({negation, R}, I, B) ->
    " ! " ++ evalu(R, I, B).

evala({self,Att}, _, _) ->
    Att ++ "[_i]";
evala({att,Att}, _,_) ->
    Att ++ "[_j]";
evala({parenthesis,P},I, B) ->
    "(" ++ evala(P,I, B) ++ ")";
evala({bracket,E}, I, B) ->
    "[" ++ evala(E,I, B) ++ "]";
evala({bracket2,E}, I, B) ->  %set as vector
    "[" ++ evala(E,I, B) ++ "]";
evala({head,Name}, I, B) -> evala(Name,I,B) ++ ".head";
evala({tail,Name}, I, B) -> evala(Name,I,B) ++ ".tail";
evala({selector,List,Index}, I,B) -> evala(List,I,B) ++ "[" ++ evala(Index,I,B) ++ "]";
evala({length, R}, I, B) ->
    evala(R, I, B) ++ ".length";
evala("true", _,_) -> "true";
evala("false", _,_) -> "false";
evala(empty_vector, _,_) -> "[]";
evala(empty_set, _,_) -> "[]"; %%currently use vector for set
evala({const,C}, _,_) -> C;
evala({minusconst,C}, _,_) -> "-" ++ C;
evala({'++',L,R}, I, B) ->
    evala(L,I,B) ++ "+" ++ evala(R,I,B);
evala({'+',L,R}, I, B) ->  % ordered set operation
    evala(L,I,B) ++ "+" ++ evala(R,I,B);
evala({'--',L,R}, I, B) ->
    evala(L,I,B) ++ "-" ++ evala(R,I,B);
evala({'-',L,R}, I, B) ->
    evala(L,I,B) ++ "-" ++ evala(R,I,B);
evala([], _,_) -> "[]";
evala({literal, T}, I, B) ->
    %io:format("information before build ~p ~p ~p~n",[T,I,B]),
    case proplists:get_value(T,B) of
	undefined ->
	    T ++ "[_i]";
	_ ->
	    "bound[_i][" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]"
    end;
evala({token,T}, _,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evala({eq, L, R}, I,B) ->
    evala(L, I, B) ++ " == " ++ evala(R, I, B);
evala({diff, L, R}, I, B) ->
    evala(L, I, B) ++ " != " ++ evala(R, I, B);
evala({ge, L, R}, I, B) ->
    evala(L, I, B) ++ " > " ++ evala(R, I, B);
evala({geq, L, R}, I, B) ->
    evala(L, I, B) ++ " >= " ++ evala(R, I, B);
evala({le, L, R}, I, B) ->
    evala(L, I, B) ++ " < " ++ evala(R, I, B);
evala({leq, L, R}, I, B) ->
    evala(L, I, B) ++ " <= " ++ evala(R, I, B);
evala({intersect, L, R}, I, B) ->
    evala(L, I, B) ++ " and " ++ evala(R, I,B);
evala({union, L, R}, I, B) ->
    evala(L, I, B) ++ " or " ++ evala(R, I, B);
evala({negation, R}, I, B) ->
    " not " ++ evala(R, I, B);
evala({ismember, L, R}, I, B) ->
    L1 = evala(L, I, B),
%    io:format("lef side ~p~n",[L]),
    R1 = evala(R, I, B),
    L1 ++ " in " ++ R1;
    %% Temp = [L1 ++ "=" ++R1++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
    %% Member = "(false or " ++ string:join(Temp, " or ") ++ ")";
evala({notmember, L, R}, I, B) ->
    "not " ++ evala({ismember, L, R}, I, B);
evala({var,Name}, _, B) ->
    I1 = proplists:get_value(Name,B),
    if is_integer(I1) -> "_m["++integer_to_list(I1)++"]";
       true  -> I1
    end.

evala({parenthesis,P},I, V,B) ->
    "(" ++ evala(P,I, V,B) ++ ")";
evala({bracket,E}, I, V,B) ->
    "[" ++ evala(E,I, V,B) ++ "]";
evala({bracket2,E}, I, V,B) ->  %set as vector
    "[" ++ evala(E,I, V,B) ++ "]";
evala({head,Name}, I, V,B) -> evala(Name,I,V,B) ++ ".head";
evala({tail,Name}, I, V,B) -> evala(Name,I,V,B) ++ ".tail";
evala({selector,List,Index}, I,V,B) -> evala(List,I,V,B) ++ "[" ++ evala(Index,I,V,B) ++ "]";
evala("true", _,_,_) -> "true";
evala("false", _,_,_) -> "false";
evala({self,Att}, I, V,B) ->
    Att ++ "[cid]";
evala({literal,Att},_, _,_) -> Att ++ "[_j]";
evala({const,C},_, _,_) -> C;
evala({minusconst,C}, _,_,_) -> "-" ++ C;
evala({'+',L,R}, I, V, B) -> evala(L,I,V,B) ++ "+" ++ evala(R,I,V,B);
evala({'*',L,R}, I, V, B) -> evala(L,I,V,B) ++ "*" ++ evala(R,I,V,B);
evala([],_,_,_) -> "[]";
evala({param,T}, I,_, B) ->
    "bound[cid]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]";
evala({token,T}, _,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evala({concat,L,R}, I, V,B) ->
    evala(L,I,V,B) ++ "+"  ++ evala(R,I,V,B);
evala({eq, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " == " ++ evala(R, I, V,B);
evala({diff, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " != " ++ evala(R, I, V,B);
evala({ge, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " > " ++ evala(R, I, V,B);
evala({geq, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " >= " ++ evala(R, I, V,B);
evala({le, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " < " ++ evala(R, I, V,B);
evala({intersect, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " and " ++ evala(R, I, V,B);
evala({union, L, R}, I, V,B) ->
    evala(L, I, V,B) ++ " or " ++ evala(R, I, V,B);
evala({negation, R}, I, V,B) ->
    " not " ++ evala(R, I, V,B);
evala({var,Name}, _, V,B) ->
    I1 = proplists:get_value(Name,V,B),
    if is_integer(I1) -> "_m["++integer_to_list(I1)++"]";
       true  -> I1
    end;
evala({ismember, L, R}, I, V,B) ->
    L1 = evala(L, I, V,B),
    R1 = evala(R, I, V,B),
    Temp = [L1 ++ "=" ++R1++"["++integer_to_list(Int)++"]" || Int <- lists:seq(0,7)],
    Member = "(" ++ string:join(Temp, " and ") ++ ")".


build_pc_guard({},{P, V}) ->
    "pc[_i][" ++ integer_to_list(P) ++ "] == " ++ integer_to_list(V);
build_pc_guard(Parent, {P, V}) ->
    build_parent(Parent) ++ "pc[_i][" ++ integer_to_list(P) ++ "] == " ++ integer_to_list(V).

% actually there is only one parent length(L) = 1
build_parent({P,V}) ->
    "pc[_i][" ++ integer_to_list(P) ++ "] == " ++ integer_to_list(V) ++ " && ".


build_pc_list(L) ->
    build_pc_list(L,[]).

build_pc_list([],L) ->
    "[" ++ string:join(L,",") ++ "]";
build_pc_list([H|T],L) ->
    print("NUM PROCS: "),
    print(H),
    H1 = lists:seq(1,H),
    S = ["1" || _ <- H1],
    String = "[" ++ string:join(S, ",") ++ "]",
    build_pc_list(T,[String | L]).

build_choice_list(N) ->
    L = lists:seq(1,N),
    S = ["[1]" || _ <- L],
    "[" ++ string:join(S,",") ++ "]".


%% evaluation of eval send
evals({parenthesis,P}, I, B, Atts) ->
    "(" ++ evals(P, I, B, Atts) ++ ")";
evals({bracket,E}, I, B, Atts) ->
    "[" ++ evals(E,I, B, Atts) ++ "]";
evals({bracket2,E}, I, B, Atts) -> %% sets as vector
    "[" ++ evals(E,I, B, Atts) ++ "]";
evals({head,N}, I, B, Atts) -> evals(N,I,B, Atts) ++ ".head";
evals({tail,N}, I, B, Atts) -> evals(N,I,B, Atts) ++ ".tail";

%% NEED TO REVIEW
evals({selector,List,Index}, I,B, Atts) -> evals(List,I,B, Atts) ++ "[" ++ evals(Index,I,B, Atts) ++ "]";
evals("true",_, _,_) -> "true";
evals("false",_, _,_) -> "false";
evals({literal,Name}, I, B, Atts) -> %may be other attributes or varibales
    case lists:member(Name,Atts) of
	true ->
	    Name ++ "[_j]";
	false ->
	    "bound[_i][" ++ integer_to_list(I) ++ "]" ++ "[" ++ integer_to_list(proplists:get_value(Name,B)) ++"]"
    end;
evals({param,T}, I, B,_) ->
    "bound[_i][" ++ integer_to_list(I) ++ "]" ++ "[" ++ integer_to_list(proplists:get_value(T,B)) ++"]";
evals({self,Att}, _,_,_) ->
    Att ++ "[_i]";
evals({'+',L,R}, I, B, Atts) ->
    evals(L,I,B,Atts) ++ "+" ++ evals(R,I,B, Atts);
evals({'*',L,R}, I, B, Atts) ->
    evals(L,I,B, Atts) ++ "*" ++ evals(R,I,B, Atts);

evals({const,C}, _,_,_) -> C;
evals({minusconst,C},_,_,_) -> "-" ++ C;
evals([],_, _,_) -> "[]";
evals({token,T},_, _,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evals([{self,Att}=Term], I,B, Atts) ->
    "[" ++ evals(Term, I,B, Atts) ++ "]";
evals([{var,Att}=Term], I,B, Atts) ->
    "[" ++ evals(Term, I,B, Atts) ++ "]";

evals([H|T]=List,I,B, Atts) when T =/= [] ->
    S = [evals(Name,I,B, Atts) || Name <- List],
    "[" ++ string:join(S,",") ++ "]";

evals({eq, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " == " ++ evals(R, I,B, Atts);
evals({diff, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " != " ++ evals(R, I,B, Atts);
evals({ge, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " > " ++ evals(R, I,B, Atts);
evals({geq, L, R}, I,B, Atts) ->
    evals(L, I,B,Atts) ++ " >= " ++ evals(R, I,B, Atts);
evals({leq, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " <= " ++ evals(R, I,B, Atts);
evals({le, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " < " ++ evals(R, I,B, Atts);
evals({intersect, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " && " ++ evals(R, I,B, Atts);
evals({union, L, R}, I,B, Atts) ->
    evals(L, I,B, Atts) ++ " || " ++ evals(R, I,B, Atts);
evals({notmember, L, R}, I,B, Atts) ->
    "not " ++ evals({ismember, L, R}, I,B, Atts);
evals({ismember, L, R}, I,B, Atts) ->
    L1= evals(L, I,B, Atts),
    R1 = evals(R, I,B, Atts),
    L1 ++ " in " ++ R1;
evals({negation, T}, I,B, Atts) ->
    " not " ++ evals(T,I,B, Atts).

%% evaluation of eval receive predicate
evalr({parenthesis,P}, I, B, M, A) ->
    "(" ++ evalr(P, I, B, M, A) ++ ")";
%% evalr({bracket,E}, I, B, M, A) ->
%%     "[" ++ evalr(E,I,B, M, A) ++ "]";
%% evalr({bracket2,E}, I, B, M) ->  %set as vector for now
%%     "[" ++ evalr(E,I,B, M) ++ "]";
%% evalr({head,N}, I, B, M) -> evalr(N,I,B,M) ++ ".head";
%% evalr({tail,N}, I, B, M) -> evalr(N,I,B,M) ++ ".tail";

%% NEED TO REVIEW
%evalr({selector,List,Index}, I,B,M) -> evalr(List,I,B,M) ++ "[" ++ evalr(Index,I,B,M) ++ "]";
evalr("true", _,_,_,_) -> "true";
evalr("false",_, _,_,_) -> "false";
evalr({param,T},I,B,_,_) ->
    "bound[_i]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]";
evalr({self,Att}, I,_,M, A) ->
    Att ++ "[_i]";
evalr({'+',L,R}, I,B,M, A) ->
    evalr(L,I,B,M, A) ++ "+" ++ evalr(R,I,B,M, A);
evalr({'-',L,R}, I,B,M, A) ->
    evalr(L,I,B,M,A) ++ "-" ++ evalr(R,I,B,M, A);
evalr({'*',L,R}, I,B,M, A) ->
    evalr(L,I,B,M, A) ++ "*" ++ evalr(R,I,B,M, A);

evalr({const,C}, _,_,_,_) -> C;
evalr([], _,_,_,_) -> "[]";
evalr({token,T}, _,_,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
evalr([{self,Att}=Term], I,B,M, A) ->
    "[" ++ evalr(Term, I,B,M, A) ++ "]";

evalr([H|T]=List,I,B,M, A) when T =/= [] ->
    S = [evalr(Name,I,B,M, A) || Name <- List],
    "[" ++ string:join(S,",") ++ "]";

evalr({eq, L, R}, I,B,M, A) ->
    evalr(L, I,B,M, A) ++ " == " ++ evalr(R, I,B,M, A);
evalr({diff, L, R}, I,B,M, A) ->
    evalr(L, I,B,M,A) ++ " != " ++ evalr(R, I,B,M,A);
evalr({ge, L, R}, I,B,M,A) ->
    evalr(L, I,B,M,A) ++ " > " ++ evalr(R, I,B,M,A);
evalr({geq, L, R}, I,B,M,A) ->
    evalr(L, I,B,M,A) ++ " >= " ++ evalr(R, I,B,M,A);
evalr({le, L, R}, I,B,M,A) ->
    evalr(L, I,B,M,A) ++ " < " ++ evalr(R, I,B,M,A);
evalr({leq, L, R}, I,B,M,A) ->
    evalr(L, I,B,M,A) ++ " <= " ++ evalr(R, I,B,M,A);
evalr({intersect, L, R}, I,B,M,A) ->
    evalr(L, I,B,M,A) ++ " && " ++ evalr(R, I,B,M,A);
evalr({union, L, R}, I,B,M,A) ->
    evalr(L, I, B,M,A) ++ " || " ++ evalr(R, I,B,M,A);
evalr({negation, T}, I, B,M,A) ->
    " !" ++ evalr(T,I,B,M,A);
evalr({literal,T}, I, B, M, A) ->
    case lists:member(T,A) of
	true ->
	    T ++ "[_j]";
	false ->
	    print(T),
	    print(A),
	    I1 = proplists:get_value(T,M),
	    case I1 of
		undefined ->
		    "bound[_i]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]";
		_ ->
		    "_m["++integer_to_list(I1)++"]"
	    end
    end.


build_msg(Exps,I, B, A) ->
    build_msg(Exps, I, B, A, []).

build_msg([],_,_, _, S) -> %
    S2 = lists:map(fun({I,{E1,E}}) ->
			   E1 ++ "_m[" ++ integer_to_list(I) ++ "] = " ++ E;
		      ({I,E}) ->
			   "_m[" ++ integer_to_list(I) ++ "] = " ++ E
		   end,
		   lists:zip(lists:seq(0,length(S)-1),lists:reverse(S))),
    Elem = "int _m[" ++ integer_to_list(length(S)) ++ "];\n      " ++ string:join(S2,";\n      ") ++ ";",
    Elem;
build_msg([H|T], I, B, A, S) ->
    build_msg(T,I,B,A,[evale(H,I,B,A)|S]).

%% UMC does not support sending compound expressions
%% Thus need to represent them as temporal variables

evale([E], I,B, A) -> % E is wrapped by a parenthesis
    "(" ++ evale(E, I,B, A) ++ ")";
evale({'+',L,R}, I,B, A) -> evale(L,I,B, A) ++ "+" ++ evale(R,I,B, A);
evale({'*',L,R}, I,B, A) -> evale(L,I,B, A) ++ "*" ++ evale(R,I,B, A);
evale({'-',L,R}, I,B, A) -> evale(L,I,B, A) ++ "-" ++ evale(R,I,B, A);
evale({'--',L,R}, I,B, A) -> evale(L,I,B, A) ++ "-" ++ evale(R,I,B, A);
evale({'++',L,R}, I,B, A) -> evale(L,I,B, A) ++ "+" ++ evale(R,I,B, A);
evale({selector,List,Index}, I,B, A) -> evale(List,I,B, A) ++ "[" ++ evale(Index,I,B, A) ++ "]";
evale({self,Att}, _,_,_) -> Att ++ "[_i]";
evale({literal,T}, I,B, A) ->
    case lists:member(T,A) of
	true ->
	    T ++ "[_i]";
	false ->
	    case proplists:get_value(T,B) of
		undefined ->
		    io:format("== I can't translate literal ~p !!~n",[T]),
		    error("Translation Error");
		V ->
		    "bound[_i]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(V) ++ "]"
	    end
    end;
evale({param,T}, I,B, A) ->
        "bound[_i]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]";
evale({var,T}, I,B, A) ->
        "bound[_i]" ++ "[" ++ integer_to_list(I) ++ "][" ++ integer_to_list(proplists:get_value(T,B)) ++ "]";
evale({const,C}, _,_,_) -> C;
evale({minusconst,C},_, _,_) -> "-" ++ C;
evale({token,T}, _,_,_) ->
    L = get(token),
    put(token, L#{T => T}),
    T.

remove_dups([])    -> [];
remove_dups([{Fi,Se,Th,_}=H|T]) -> [H | [X || {Fi1,Se1,Th1,_}=X <- remove_dups(T), {Fi1,Se1,Th1} /= {Fi,Se,Th}]].

print(X) -> io:format("~p~n", [X]).
