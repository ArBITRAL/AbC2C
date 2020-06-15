-module(abc2c).
-export([file/1, main/1, view/1]).
-record(state,{parent, entry, aware, exit, act_index, bound_index, bound, v_name, nil}).

print(X) -> io:format("~p~n", [X]).

%% build the project
main(["build"]) ->
	leex:file(scanner),
	yecc:file(parser);
main([Fname]) -> file(Fname);
main(["scan", Fname]) ->
	{ok, Binary} = file:read_file(Fname),
	print(scanner:string(binary_to_list(Binary))).

%% run a file name
file([Atom]) when is_atom(Atom) ->
    file(v(Atom) ++ ".abc");
file(Fname) ->
    {ok, Binary} = file:read_file(Fname),
    trans(binary_to_list(Binary), Fname).

view([Atom]) when is_atom(Atom) ->
    view(v(Atom) ++ ".abc");
view(Fname) ->
    {ok, Binary} = file:read_file(Fname),
    view1(binary_to_list(Binary)).
view1(Code) ->
    {ok, Tree} = parser:scan_and_parse(Code),
    io:format("~p~n",[Tree]).

%% translate the code
trans(String, Outname) when is_list(String) ->
    {ok, Tree} = parser:scan_and_parse(String), % get AST

    %% extract necessary system structure
    Sys = [Y || {sys, Y} <- Tree], % Considering those components are declared under SYS
    CompDefs = [X || X <- Tree, element(1,X) == comp], % component definitions
    Comp_inits = [X || X <- Tree, element(1,X) == comp_init], % component instantiations
    CNames = [X || {comp, X, _} <- CompDefs], % component names
%%    print(Comp_inits),
    ets:new(abcsystem,[named_table]), %% the table that keeps all
    ets:new(cmodel,[named_table]), %% the table that store trasnlated code
    ets:new(counter1,[named_table]),
    ets:new(counter2,[named_table]),

    %% Store code definitions
    preprocessing(CompDefs, Comp_inits), % FULL OF SIDE-EFFECTS!
    AttEnv = ets:lookup_element(abcsystem, attributes, 2),

    {IdRange, TotalComps} = lists:mapfoldl(fun(X, A) -> {{A, ["N_" ++ v(X) | A]}, ["N_" ++ v(X) | A]} end, [], CNames),


    ets:insert(cmodel,{body,[]}),
    body(lists:zip(IdRange,CNames)), % the main work, collect code for component behaviour

    ets:insert(cmodel,{init,[]}),
    PnList = c_init(Comp_inits, Sys), % collect code for components initialization

    header(PnList, TotalComps, AttEnv), % code for the header C file/ global definitions
    output_model(Outname). % out put file


body(Beh) ->
    body(Beh, []).

body([], ActTables) ->
    out_behcode(lists:reverse(ActTables)),     %% finish translating behaviour

    Drivers = get_driver_code(),
    out_behcode(["\n// ---------- DRIVERS ------------ \n",Drivers]);

%% translate each component type!
body([{IdRange,CName}|Rest], ActTables) ->
    ets:insert(counter1,{c,0}),
    ets:insert(counter2,{c,0}),
    ets:insert(CName, {num_indexes, 0}),
    ets:insert(CName, {num_vars, #{}}),
    ets:insert(CName, {stable, []}),
    ets:insert(CName, {rtable, []}),
    ets:insert(CName, {id_range, id_range(IdRange)}),
    InitBehaviour = ets:lookup_element(CName, init_beh, 2), % gets the init behaviour of component
    % storing the number of processes in this component type, abusing for determining process index init = 0

    %% main process index and counter
    %% force using Component name as process name in the begining
    %% Note that bound index is different from Pc index, they increase their values differently
    %% there is no parent in the first time
    ProcessState = CName,
    Process = #{parent => {}, %% pair of parent index and exit point
		v_name => [], % proplist contain variables in the received message and its index
		cnt => 0},

    ets:insert(ProcessState, {state, Process}), % representing state of a sequential process: prefixing, choice, recursion
    ets:insert(CName, {visited, []}), % the init process have the same name as component name

    Print = "\n// ---------- COMPONENT " ++ v(CName) ++ " ------------ \n",

    out_behcode(Print),

    call(InitBehaviour, CName, ProcessState),

    %% Collect action tables
    ST = lists:reverse(ets:lookup_element(CName, stable, 2)),
    RT = lists:reverse(ets:lookup_element(CName, rtable, 2)),


    PrintST = "\npts st_" ++ v(CName) ++ "[] = {" ++ string:join(lists:map(fun({_,Y}) -> "&" ++ Y end, ST), ",") ++ "};\n",
    PrintRT = "\nptr rt_" ++ v(CName) ++ "[] = {" ++ string:join(lists:map(fun({_,Y}) -> "&" ++ Y end, RT), ",") ++ "};\n\n",

    Print2 = ["\n// ---------- Action Table " ++ v(CName) ++ " ------------ \n", PrintST, PrintRT],

    %% translate the behaviour of the component here


    body(Rest, [Print2 | ActTables]).

%% Helper functions
%% Entry = {[parent process],entry value for transition}
call(Code, CName, ProcessState) ->
    %% carry out the information as how to produce code for an action
    ActionState = #state{parent = {}, % pair of parent index and exit point
			 aware = [], % no awareness yet
			 entry = 0,   % entry point initialized as 0
			 exit = -1, % calculate exit point by itself
			 act_index = 0,
			 v_name = [],
			 bound_index = 0, %% index of bound variables in a bound vector
			 nil = 0 %detech nill continuation, reset bound variables??
			},
%    io:format("translate for component ~p with code ~p and Procs State ~p ~n",[CName, Code, ProcessState]),
    eval(Code, CName, ProcessState, ActionState).


eval({proc, ProcName, Args, Code, Times}, CName, ProcessState, ActionState) when Times > 0 ->
    %%  overriden definition for translating bang
    ets:insert(CName, {ProcName, {proc, Args, Code}}),
    %% need to restore later
    %% start with no previous instances []
    eval({bang, ProcName, Args, Code, Times + 1, Times + 1, []}, CName, ProcessState, ActionState);
eval({proc, _Args, Code}, CName, ProcessState, ActionState) ->
    %%% process definition with Args list, the formal parameter may have different names compared to actual parameters in Bound
    eval(Code, CName, ProcessState, ActionState);

%% the execution model : call a process, then trace the proc definition to unfold
eval({call, ProcName, _Args}, CName, ProcessState, ActionState = #state{entry = Evalue, act_index = AIndex}) ->
    ProcInstance = {ProcName, AIndex},
    Visited = ets:lookup_element(CName, visited, 2),
    %% check if this process instance has already been visited
    case proplists:lookup(ProcInstance, Visited) of
	none ->
	    ets:insert(CName, {visited, [{ProcInstance, Evalue} | Visited]});
	_ ->
	    ok
    end,
    BI = length(ets:lookup_element(CName, visited, 2)) - 1, %% compute index of ProcName definitions, used for storing bound variables
    Code = ets:lookup_element(CName, ProcName, 2),
    eval(Code, CName, ProcessState, ActionState#state{bound_index = BI, v_name = []});

eval({choice,P,Q}, CName, ProcessState, ActionState) ->
    eval(P, CName, ProcessState, ActionState),
    eval(Q, CName, ProcessState, ActionState);


%% translation of parallel processes

%%% there are two cases to be considered

%% CASE 1: processes are created without a prefix action, thus, entry = 0

eval({par, P, Q}, CName, ProcessState, ActionState = #state{entry = 0}) ->
    % resuse index
    AIndex1 = ets:lookup_element(CName,num_indexes,2),
  %  io:format("parallel of ~p and ~p at index = ~p ~n", [P, Q, AIndex1]),

    % creating new processState for each P and Q
    M = ets:lookup_element(ProcessState,state,2),

    Child1 = v(CName) ++ v(AIndex1),

    ProcessState1 = ets:new(list_to_atom(Child1),[]),
    ets:insert(ProcessState1, {state, M#{cnt := 0}}),

    eval(P, CName, ProcessState1, ActionState#state{act_index = AIndex1}),

    ets:update_counter(CName, num_indexes, 1), % bc index started from 0

    AIndex2 = ets:lookup_element(CName,num_indexes,2),

    Child2 = v(CName) ++ v(AIndex2),
    ProcessState2 = ets:new(list_to_atom(Child2),[]),
    ets:insert(ProcessState2, {state, M#{cnt := 0}}),
    eval(Q, CName, ProcessState2, ActionState#state{act_index = AIndex2});

%% CASE 2: processes are created with a prefix action, thus, entry = Cnt which acts as a parent exit point, entry points of all parallel processes must include their parent exit point
%% REVIEW
eval({par, P, Q}, CName, ProcessState, ActionState = #state{act_index = AIndex, entry = Cnt}) ->
    ets:update_counter(CName, num_indexes, 1), % bc index started from 0
    AIndex1 = ets:lookup_element(CName,num_indexes,2),
    io:format("parallel of ~p and ~p at index = ~p, entry = ~p ~n", [P, Q, AIndex,Cnt]),
    M = ets:lookup_element(ProcessState,state,2),
    Child1 = v(CName) ++ v(AIndex1),
    ProcessState1 = ets:new(list_to_atom(Child1),[]),
    ets:insert(ProcessState1, {state, M#{cnt := 0}}),
    eval(P, CName, ProcessState1, ActionState#state{parent = {AIndex, Cnt}, entry = 0, exit = -1, act_index = AIndex1}),
    ets:update_counter(CName, num_indexes, 1), % bc index started from 0

    AIndex2 = ets:lookup_element(CName,num_indexes,2),
    Child2 = v(CName) ++ v(AIndex2),
    ProcessState2 = ets:new(list_to_atom(Child2),[]),
    ets:insert(ProcessState2, {state, M#{cnt := 0}}),
    eval(Q, CName, ProcessState2, ActionState#state{parent = {AIndex, Cnt}, entry = 0, exit = -1, act_index = AIndex2});

%% TODO : recognize P | P
%% replicate P Time times
eval({bang, ProcName, Args, Code, Times, T, _}, CName, _, _) when T =< 0 -> %stop at 0 because we counted Q in P = Q |^n P
%    io:format("translate bang at Copies = ~p, has finished ~n",[T]),
    %% update numprocs because we are not going to generate for code at index -1
    ets:update_counter(CName, num_indexes, -1),
    %% restore overriden code
    ets:insert(CName, {ProcName, {proc, ProcName, Args, Code, Times - 1}}),
    %%ets:insert(CName, {ProcName, {proc, Args, Code, Times}}),
    ok;
eval({bang, ProcName, Args, Code, Total, Times, PrevInstance}, CName, ProcessState, ActionState) when Times > 0 ->
    AIndex1 = ets:lookup_element(CName,num_indexes,2),
%    io:format("translate bang for ~p, at Copies = ~p, newest index ~p, previous instances index ~p ~n",[ProcName,Times,AIndex1,PrevInstance]),
    M = ets:lookup_element(ProcessState,state,2),
    Child1 = v(CName) ++ v(AIndex1),
    ProcessState1 = ets:new(list_to_atom(Child1),[]),
    ets:insert(ProcessState1, {state, M#{cnt := 0}}),
    eval({call, ProcName, Args}, CName, ProcessState1, ActionState#state{entry = 0, act_index = AIndex1}),
    ets:update_counter(CName, num_indexes, 1),
    eval({bang, ProcName, Code, Args, Total, Times - 1, AIndex1}, CName, ProcessState, ActionState);

eval({p_awareness, Pred, Process}, CName, ProcessState, ActionState = #state{act_index = AIndex, parent = Parent, v_name = VName}) ->
%    #{v_name := Bound} = ets:lookup_element(ProcessState,state,2),
    P = if Parent == {} ->
		utils:build_apred(Pred, AIndex, VName);
	   true -> %% awareness of first action use variable from Parent
		{ParentIndex,_} = Parent,
		utils:build_apred(Pred, ParentIndex, VName)
	end,
    eval(Process, CName, ProcessState, ActionState#state{aware = [P| ActionState#state.aware]});

eval({prefix, Left, {call, ProcName, _Args} = Right}, CName, ProcessState, ActionState = #state{act_index = PcIndex}) ->
    ProcInstance = {ProcName, PcIndex},
    Visited = ets:lookup_element(CName, visited, 2),
    case proplists:lookup(ProcInstance, Visited) of
	{_, EntryPoint} ->
	    %% creating code for this transition, with recursion
	    build_act(Left, CName, ProcessState, ActionState#state{exit = EntryPoint});
	none ->
	    %% creating code for this action, and then proceeding with ProcName
	    {Exit, VName} = build_act(Left, CName, ProcessState, ActionState),
	    %% reset the state for the next action, i.e., there no aware anymore
	    eval(Right, CName, ProcessState, ActionState#state{entry = Exit, parent = {}, aware = [], v_name = VName})
    end;

eval({prefix, Left, nil}, CName, ProcessState, ActionState) -> % Right is a nil process
%    io:format("Next is nil~n"),
    %% creating code for this action, and then proceeding with ProcName
    build_act(Left, CName, ProcessState, ActionState#state{nil = 1}),
    ok;
eval({prefix, Left, Right}, CName, ProcessState, ActionState) -> % Right is a choice process
    %% creating code for this action, and then proceeding with ProcName
    {Exit, VName} = build_act(Left, CName, ProcessState, ActionState),
    %% reset the state for the next action, i.e., there no aware anymore
    eval(Right, CName, ProcessState, ActionState#state{entry = Exit, parent = {}, aware = [], v_name = VName});

%% may be never get in here
eval(nil, _, _, _) ->
    ok;
eval(FINAL, CName, ProcessState, ActionState) ->
    io:format("FINAL DOES NOT MATCH, ~p ~p ~p ",[FINAL, CName, ActionState]).


%% empty send ()@(ff)
build_act({{output, empty, empty}, Upd}, CName, ProcessState,
	     #state{parent = Parent,
		    entry = Value,
		    aware = Aware,
		    exit = ExitPoint,
		    bound_index = BI,
		    act_index = AIndex}) ->
    Signal = " \n// -----Empty Send ----- \n",

    Map = ets:lookup_element(ProcessState, state, 2),
    #{cnt := Cnt, v_name := Bound}  =  Map,

    Updates = if Upd == [] -> ""; true -> "\n//  --- attr update --- \n  " ++ utils:build_update(Upd, AIndex, Bound) ++ ";\n  "  end,
    PAware = if Aware == [] -> ""; true -> " && " ++ string:join(Aware," && ") end,

    Cond = utils:build_pc_guard(Parent, {AIndex, Value}),

    Fname = fresh(snd,CName) ++ " {\n  ",
    Guards = "if {" ++  PAware  ++ Cond ++ "} {\n  ",

    Exit = if ExitPoint > 0 -> ExitPoint; true -> Cnt + 1 end,

    Actions = Updates ++ "\n  " ++ exec_point(AIndex,Exit) ++ ";}\n}\n",
    ets:insert(ProcessState, {state, Map#{cnt := if ExitPoint > 0 -> Cnt; true -> Cnt + 1 end}}),

    Print = [Signal, Fname, Guards, Actions],
    out_behcode(Print),
    Exit;

build_act({{output, Exps, Pred}, Upd}, CName, ProcessState,
	     #state{parent = Parent,
		    entry = Value,
		    aware = Aware,
		    exit = ExitPoint,
		    bound_index = BI,
		    v_name = VName,
		    act_index = AIndex}) ->

    Signal = " \n// ----- Send ----- ",
    Map = ets:lookup_element(ProcessState, state, 2),

    #{cnt := Cnt, v_name := Bound}  =  Map,

    PAware = if Aware == [] -> ""; true -> " && " ++ string:join(Aware," && ") end,
    %%io:format("built _aware ~p where bound vars ~p ~n",[Aware, Bound]),

    %% io:format("build _update ~p where bound vars ~p ~n",[Upd, Bound]),
    %%  io:format("update is ~p ~n",[Updates]),
    Cond = utils:build_pc_guard(Parent, {AIndex, Value}),
    FName = fresh(snd,CName),

    {BeginId, EndId} =  ets:lookup_element(CName, id_range, 2),

    FSign = "\nint " ++ FName ++ "(int _i, int _f) {\n",
    ProtectId = "  if (_i >= " ++ BeginId ++ " &&  _i < " ++ EndId ++ ") {\n",
    Avai = "    if (!_f)\n      return (" ++  Cond ++  PAware  ++");\n\n",
    Guards = "    if (" ++  Cond ++ PAware  ++") {\n",

%    io:format("translate output ~p ~p ~p ~p ~n",[Exps, Pred, Cnt, Value]),
    Msg = utils:build_msg(Exps, BI, VName, my_attrs(CName)),
   %% io:format("msg to be send ~p ~n",[Msg]),
    Output = "      " ++ Msg ++ "\n      Sync(_i,_m);\n",

    SndP = utils:build_spred(Pred, BI, VName, other_attrs(CName)),
    %%% if there any membership predicate
    Tgt = "      for (int _j= 0; _j < N; _j++)" ++
       "\n        if (_j != _i && " ++ SndP ++ ") \n\t  tgt[_j] = 1;\n\telse\n\t  tgt[_j] = 0;\n\n",

    Updates = if Upd == [] -> ""; true -> "      //--- attr update --- \n    " ++ utils:build_update(Upd, BI, VName) ++ ";\n      " end,


    %io:format("exit point of this action ~p~n",[Exit]),
    %% Recstring is different if there is Recursive from <pi>P or [a:=e]px


    Exit = if ExitPoint == -1 -> Cnt+1; true  ->  ExitPoint end,

    %io:format("exit point of this action ~p~n",[Exit]),
    %% Recstring is different if there is Recursive from <pi>P or [a:=e]px
    Actions = Guards ++ Tgt ++ Output ++ Updates ++ "\n      " ++ exec_point(AIndex,Exit) ++ ";\n      return 1;\n    }\n  }\n  return 0;\n}",

    Print = [Signal, FSign, ProtectId, Avai, Actions],

    ST = ets:lookup_element(CName, stable, 2),
    ets:insert(CName, {stable, [{AIndex, FName} | ST]}),

%%    io:format("Send Act ~p, added to table ~p ~n",[ST,ets:lookup_element(CName, stable, 2)]),

    out_behcode(Print),

    ets:insert(ProcessState, {state, Map#{cnt => if ExitPoint == -1 -> Cnt + 1; true -> Cnt end}}),
    {Exit, VName};

build_act({{input, Pred, Vars}, Upd}, CName, ProcessState,
	     #state{parent = Parent,
		    entry = Value,
		    aware = Aware,
		    exit = ExitPoint,
		    bound_index = BI,
		    v_name = VName,
		    act_index = AIndex}) ->
    Signal = "\n\n// ----- Receive ----- ",

    Map  = ets:lookup_element(ProcessState,state,2),
    #{cnt := Cnt} = Map,
    NumVars = ets:lookup_element(CName,num_vars,2),
     %% accumulate received Vars
    ets:insert(CName,{num_vars,maps:update_with(BI, fun(V) -> Vars ++ V end, Vars, NumVars)}),

    %%io:format("Trans input, exit point ~p, cnt = ~p, entry = ~p ~n",[ExitPoint, Cnt, Value]),

    [BoundAssignments, NewBound, Msg] = bound_assignment(VName, Vars, v(BI)),
%%    print(BoundAssignments),
 %%   print(NewBound),
  %%  print(Msg),
   %% print(Bound),
    %%print(BI),

    PAware = if Aware == [] -> ""; true -> " && " ++ string:join(Aware," && ")  end,
    Cond = utils:build_pc_guard(Parent, {AIndex, Value}),

    {BeginId, EndId} =  ets:lookup_element(CName, id_range, 2),

    FName = fresh(recv,CName),
    FSign = "\nint " ++ FName ++ "(int _i, int _j, int* _m) {\n",

    ProtectId = "  if (_i >= " ++ BeginId ++ " &&  _i < " ++ EndId ++ ") {\n  ",

    print(other_attrs(CName)),
    RcvP = utils:build_rpred(Pred, BI, VName, Msg, other_attrs(CName)),
    Guards = "  if (" ++ Cond ++ PAware ++ RcvP  ++ ") {\n      ",

    Updates = if Upd == [] -> ""; true -> "\n      //--- attr update --- \n      " ++ utils:build_update(Upd, BI, NewBound) ++ ";\n" end,

    Exit = if ExitPoint == -1 -> Cnt + 1;  % no recursion, use 1 counter value
	      true  ->  ExitPoint
	   end,

    %% add bound assignments
    %% storing variables appearing in the received messages,
    %% if a variable appear many times in the same process, the latest is stored
    RT = ets:lookup_element(CName, rtable,2),
    ets:insert(CName, {rtable, [{AIndex, FName} | RT]}),
  %%  io:format("Recv Act ~p, added to table ~p ~n",[RT,ets:lookup_element(CName, rtable, 2)]),
    %%Reset = if Nil > 0 orelse ExitPoint > 0 -> "\n\tbound[cid][" ++ v(AIndex) ++ "] := [];"; true -> "" end,
    %%Reset2 = if Nil > 0 -> "\n\t" ++ Pc ++ " := 0;"; true -> "" end,
    ExecPoint = "\n      " ++ exec_point(AIndex,Exit) ++ ";",
    Print = [Signal, FSign, ProtectId, Guards, BoundAssignments, Updates, ExecPoint,"\n      return 1;\n    }\n  }\n  return 0;\n}\n"],
    ets:insert(ProcessState, {state, Map#{v_name => NewBound, cnt => if ExitPoint  == - 1 -> Cnt + 1; true -> Cnt end}}),
%    file:write_file("foo.umc", Print, [append]),
    out_behcode(Print),
    %%io:format("translate input ~p ~p ~p ~p ~n",[Pred, Vars, Exit, Cnt]),
    {Exit, NewBound}.

preprocessing(CompDefs, Comp_inits) ->
    ets:insert(abcsystem, {attributes, #{}}),
    %% component indexes
    I = lists:seq(0,length(CompDefs) - 1),
    Comps = lists:zip(I, CompDefs),
    %% storing components behaviour definitions and initializing them into each own table
    lists:foreach(fun({I1, {comp, CName, [{attrs, AttList}, {beh, Behaviour, Init}]}}) -> % FULL OF SIDE-EFFECT
		      %% each component has an information table
		      ets:new(CName, [named_table]),
		      %% store the init behaviour of component definition CName
		      ets:insert(CName,Init),

		      %% store process definitions of this component
		      Fun = fun({def, ProcName, Args, Code}) ->
				    ets:insert(CName, {ProcName, {proc, Args, Code}});
			       ({def, ProcName, Args, Code, Times}) -> % for recursion under parallel
				    ets:insert(CName, {ProcName, {proc, ProcName, Args, Code, Times}})
			    end,
		      lists:map(Fun, Behaviour),
		      %% Create the attributes list from component definitions
		      %% Assigning component indexes to each attribute name
		      Acc = ets:lookup_element(abcsystem, attributes, 2),
		      Map = maps:put(CName, AttList, Acc),
		      ets:insert(abcsystem, {attributes, Map})
	      end, Comps),

    %% Collect attribute environments of all compnents
    Data = lists:foldl(fun({comp_init, CInit, {comp, _, Decl} = Body}, Acc) ->
			       ets:insert(abcsystem, {CInit, Body}),
			       [Decl | Acc]
		       end, [], Comp_inits),

    put(token,#{}), % for storing Tokens
    %% keep initialization data for attribute environments to output to the UMC model
    ets:insert(abcsystem, {data, Data}).

c_init(CName_inits, []) -> % there's no SYS ::= declaration
%%    print(CName_inits),
    c_init(CName_inits);
c_init(_, [SYS]) -> % there is SYS ::=
    c_init(SYS).

c_init(SYS) ->
    Index = lists:seq(0,length(SYS)-1),
    S1 = lists:zip(Index, SYS),
    init(S1,#{}, []).

init([], PnList, InitComs) ->
    Token = get(token),
    TokenDef = if Token =/= #{} ->
		       "\nenum Token = {" ++ string:join(maps:keys(Token), ", ") ++ "} \n\n";
		  true -> ""
	       end,
    %% TokenCompDef = string:join(lists:reverse(TokenComps), ",") ++ " : Token; \n\n",    Object = "OO : System (" ++ string:join(Decl, ", ") ++ ");",

%    io:format("Keys ~p, Map ~p ~n", [maps:keys(PnList), PnList]),
    IBody = make_init(maps:keys(PnList)),
    ICode ="\n\nvoid init() {\n  " ++
	string:join(lists:reverse(InitComs), ";\n  ") ++  ";\n  int _i, _j;\n  " ++ string:join(IBody, "\n  ") ++ "\n}",

    %% FBody = make_clean(maps:keys(PnList)),
    %% FCode = "\n\nvoid clean() {\n  int _i, _j;\n  " ++ string:join(FBody, "\n  ") ++ "\n}",

%%    ObserStates = string:join(lists:reverse(Observables), "\n"),
    out_initcode([ICode, TokenDef]),
    PnList;

%% chance to init components individually here
init([{Index, {comp_init, Name, _}} | Rest], PnList, AnotherTokens) ->
    {comp, CName, Data}  = ets:lookup_element(abcsystem, Name, 2),
%%    Interfaces = ets:lookup_element(CName, obsrs, 2),
%%    print(Data),
    Decl = string:join(lists:map(fun({X,V}) ->
					 X ++ "[" ++ v(Index) ++ "] = " ++ data_eval(V)
				end, Data), "; "),

    InitComp = "init" ++ v(Index) ++ "()",
    InitCode = "void " ++ InitComp ++ " {" ++ Decl ++ ";}\n",
    Print = "\n//----init " ++ v(Name) ++ " ----- \n" ++ InitCode,
%    file:write_file("foo.umc", [Print ++ M4Code], [append]),
    out_initcode(Print),
%%    io:format("Compute map ~p, Map ~p ~n", [maps:keys(PnList), PnList]),
%    Pn = ets:lookup_element(CName, num_indexes, 2) + 1, % bc Pindex starts from 0
    %% print(ParVector),
    init(Rest, maps:update_with(CName, fun(V) -> V + 1 end, 1, PnList), [InitComp | AnotherTokens]).


output_model(Outname) ->
    Header = ets:lookup_element(cmodel,header,2),
    Behaviour = lists:reverse(ets:lookup_element(cmodel,body,2)),
    Init = lists:reverse(ets:lookup_element(cmodel,init,2)),

    Property = "\n\n//---Properties--- \nvoid check_safety() {\n  _Bool safety = false;\n  __CPROVER_assert(!safety,\"\");\n}\n" ++ "\nvoid check_liveness() {\n  _Bool liveness = true;\n  __CPROVER_assert(liveness,\"\");\n}\n",
    MainLoop = "\n\nint main() {\n  init();\n  unsigned short cid;\n  while (available()) {\n    cid = schedule();\n    __CPROVER_assume(Evolve(cid));\n    check_safety();\n  }\n  check_liveness();\n  return 0;\n}\n\n",
%    io:format("====code accumulated so far==== \n ~s",[Define]),
%%   io:format("====code accumulated so far==== \n ~s",[Header]),
    [CFile|_] = string:split(Outname,"."),
    file:write_file(CFile ++ ".c", [Header, Behaviour, Init, Property, MainLoop]).


header(PnList, TotalComps, AttEnv) ->
    Atts = sets:to_list(sets:from_list(lists:append(maps:values(AttEnv)))), %% attrs set
    Type = "\n\ntypedef int (*pts)(int, int);\ntypedef int (*ptr)(int, int, int*);\n\nstruct {\n  int ns;\n  int nr;\n  pts* SendAct;\n  ptr* RecvAct;\n} lookup[N];\n\nint Evolve(int);\nvoid Sync(int, int*);\nvoid receive(int, int, int*);",
    Header = "\n#define true 1\n#define false 0\n" ++ Type ++ "\n\nint pc[N][NP_MAX] = {};\nint bound[N][ND_MAX][NV_MAX];\nint tgt[N] = {};\n\t\n// attributes\nint " ++ lists:join("[N];\nint ",Atts) ++ "[N];\nunsigned short nondet_ushort();\n_Bool nondet_bool();\n\n",
    Define = "#define N " ++ string:join(TotalComps, " + ") ++ " // # components \n\n" ++ build_define(maps:to_list(PnList)),
    ets:insert(cmodel,{header, [Define, Header]}).

build_define(A) ->
    build_define(A,0,0,0,[]).

build_define([], NP_Max, ND_Max, NV_Max, Define) ->
    Define ++
    "\n#define NP_MAX" ++ " " ++  v(NP_Max) ++ " // # max action indexes \n" ++
    "#define ND_MAX" ++ " " ++  v(ND_Max) ++ " // # max process definitions \n" ++
    "#define NV_MAX" ++ " " ++  v(NV_Max) ++ " // # bound variables (max) \n";
build_define([{CName,N} | Rest], NP_Max, ND_Max, NV_Max, Define) ->
    NumVars = maps:map(fun(K,V) -> length(lists:usort(V)) end, ets:lookup_element(CName, num_vars, 2)),
    NV = lists:max(maps:values(NumVars)),
    NP = ets:lookup_element(CName, num_indexes, 2) + 1, % index starts from 0
    ND = length(ets:lookup_element(CName, visited, 2)), % # process definitions
    NS = length(ets:lookup_element(CName, stable, 2)),
    NR = length(ets:lookup_element(CName, rtable, 2)),
    Name = v(CName),
    A = "\n#define N_" ++ Name ++ " " ++  v(N) ++ " // # components (of this type) \n",
    B = "#define NP_" ++ Name ++ " " ++  v(NP) ++ " // # action indexes \n",
    C = "#define NS_" ++ Name ++ " " ++ v(NS) ++ " // # sending actions \n",
    D = "#define NR_" ++ Name ++ " " ++ v(NR) ++ " // # receiving actions \n",
%   E = "#define ND_" ++ Name ++ " " ++  v(ND) ++ " // # process definitions \n",
%   F = "#define NV_" ++ Name ++ " " ++ v(NV) ++ " // # bound variables (max) \n\n",
    build_define(Rest, max(NP,NP_Max), max(ND,ND_Max), max(NV,NV_Max), [A ++ B ++ C ++ D  | Define]).

%% build_bound_list(L) ->
%%     build_bound_list(L,[]).

%% build_bound_list([],L) ->
%%     "[" ++ string:join(L,",") ++ "]";
%% build_bound_list([H|T],L) ->
%%     H1 = lists:seq(0,H),
%%     S = ["[]" || _ <- H1],
%%     String = "[" ++ string:join(S, ",") ++ "]",
%%     build_bound_list(T,[String | L]).


data_eval({token,T}) ->
    L = get(token),
    put(token, L#{T => T}),
    T;
data_eval({const,C}) ->
    C;
data_eval({minusconst,C}) ->
    "-" ++ C;
data_eval(empty_vector) ->
    "[]";
data_eval(empty_set) -> % set as vector for now
    data_eval(empty_vector);
% an array of single elements
data_eval({bracket2, List}) -> % set as vector for now
    data_eval({bracket, List});
data_eval({bracket, List}) when is_list(List) ->
   % io:format("eval for ~p ~n",[List]),
    Array = [data_eval(X) || X <- List],
    "[" ++ string:join(Array,",") ++ "]";
data_eval({bracket, E}) ->
    "[" ++ data_eval(E) ++ "]";
data_eval(Other) -> Other.

filter_bindings(Args, VarNames) -> % vars is the message, bindings is
    %% simplest case, Vars \in Bindings
    Name = [X || {_,X} <- Args],
    L = [{X,proplists:get_value(X,VarNames)} || X <- Name].

select_bindings(FormalArgs, ActualArgs) ->
    Vals = [I || {_,I} <- ActualArgs],
    lists:zip(FormalArgs,Vals).

%% previous vars [{x,0}, {y,1}, ...]
%% new vars  = [x, z,t,w],
%% get several things: assign variable in the message to bound, return new proplist of [{allvars , indexes}] and the message
bound_assignment([], Vars, Index) ->
    io:format("previous vars empty, got a message ~p ~n",[Vars]),
    Index1 = lists:seq(0, length(Vars) - 1),
    Msg = lists:zip(Vars, Index1),
    B1 = string:join(["bound[_i][" ++ Index ++ "][" ++ v(proplists:get_value(X,Msg)) ++ "] = _m[" ++ v(proplists:get_value(X,Msg)) ++ "];" || X <- Vars], "\n      "),
    [B1, Msg, Msg];
bound_assignment(PreviousVars, Vars, Index) ->
    Prev1 = [X || {X,_} <- PreviousVars], % previous variables
    io:format("previous vars ~p, got a message ~p ~n",[PreviousVars, Vars]),
    Added = Vars -- Prev1,  % added vars
    io:format("added vars ~p~n",[Added]),
    Length1 = length(PreviousVars),
    Index1 = lists:seq(0, length(Vars) - 1),
    Msg = lists:zip(Vars, Index1),
    Index2 = lists:seq(Length1, Length1 + length(Added) - 1),
    New = lists:zip(Added, Index2),
    New2 = PreviousVars ++ New,
%%    L = [proplists:get_value(X, PreviousVars) || X <- Vars, proplists:get_value(X) =/= undefined],
    B1 = string:join(["bound[_i][" ++ Index ++ "][" ++ v(proplists:get_value(X,New2)) ++ "] = _m[" ++ v(proplists:get_value(X,Msg)) ++ "];" || X <- Vars], "\n      "),
    io:format("boundassing ~p newbound ~p~n",[B1, New2]),
    [B1, New2, Msg].


out_behcode(Code) ->
    B = ets:lookup_element(cmodel,body,2),
    ets:insert(cmodel, {body, [Code|B]}).

out_initcode(Code) ->
    I = ets:lookup_element(cmodel,init,2),
    ets:insert(cmodel, {init, [Code|I]}).

fresh(snd, CName) ->
    C = ets:update_counter(counter1,c,1),
    "__" ++ v(CName) ++ "_a" ++ v(C);
fresh(recv, CName) ->
    C = ets:update_counter(counter2,c,1),
    "__" ++ v(CName) ++ "_b" ++ v(C).

%% make_clean(A) ->
%%     make_clean(A,[]).

%% make_clean([], Acc) ->
%%     Acc;
%% make_clean([H|T], Acc) ->
%%     {B, E} = ets:lookup_element(H, id_range, 2),
%%     make_clean(T, [make_loop2(v(H),B,E) | Acc]).

%% make_loop2(C,B,E) ->
%%     "for (_i = " ++ B ++ ";_i < " ++ E ++ ";_i++) {\n    " ++
%% 	"for (_j = 0; _j < " ++ "ND_" ++ C ++"; _j++) free(bound[_i][_j]);\n    " ++
%% 	"free(pc[_i]);\n    " ++
%% 	"free(bound[_i]);\n  }    ".

make_init(A) ->
    make_init(A,[]).

make_init([], Acc) ->
    Acc;
make_init([H|T], Acc) ->
    {B, E} = ets:lookup_element(H, id_range, 2),
    make_init(T, [make_loop(v(H),B,E) | Acc]).


%% make_loop(C,B,E) ->
%%     "for (_i = " ++ B ++ ";_i < " ++ E ++ ";_i++) {\n    " ++
%% 	"lookup[_i].ns = NS_" ++ C ++ ";\n    " ++
%% 	"lookup[_i].nr = NR_" ++ C ++ ";\n    " ++
%% 	"lookup[_i].SendAct = st_" ++ C ++ ";\n    " ++
%% 	"lookup[_i].RecvAct = rt_" ++ C ++ ";\n    " ++
%% 	"pc[_i] = (int*) malloc(sizeof(int) * NP_" ++ C ++ ");\n    " ++
%% 	"bound[_i] = (int**) malloc(sizeof(int*) * ND_" ++ C ++ ");\n    " ++
%% 	"for (_j = 0; _j < " ++ "ND_" ++ C ++"; _j++) bound[_i][_j] = (int*) malloc(sizeof(int) * NV_" ++ C ++ ");\n    " ++
%% 	"for (_j = 0; _j < " ++ "NP_" ++ C ++"; _j++) pc[_i][_j] = 0;\n   }".


make_loop(C,B,E) ->
    "for (_i = " ++ B ++ ";_i < " ++ E ++ ";_i++) {\n    " ++
	"lookup[_i].ns = NS_" ++ C ++ ";\n    " ++
	"lookup[_i].nr = NR_" ++ C ++ ";\n    " ++
	"lookup[_i].SendAct = st_" ++ C ++ ";\n    " ++
	"lookup[_i].RecvAct = rt_" ++ C ++ ";}".

other_attrs(CName) ->
    %% other attributes should be all attributes
    Attrs = ets:lookup_element(abcsystem, attributes, 2),
    Others = lists:append([X || {O,X} <- maps:to_list(Attrs)]).

my_attrs(CName) ->
    Attrs = ets:lookup_element(abcsystem, attributes, 2),
    My = lists:append([X || {O,X} <- maps:to_list(Attrs), O == CName]).


exec_point(I,V) ->
    "pc[_i][" ++ v(I) ++ "] = " ++ v(V).


v(V) when is_integer(V) ->
    integer_to_list(V);
v(A) when is_atom(A) ->
    atom_to_list(A).


id_range({[], End}) ->
    {"0", End};
id_range({Begin, End}) ->
    {string:join(Begin," + "), string:join(End," + ")}.


get_driver_code() ->
    "int Evolve(int _i) {
  pts* _sa = lookup[_i].SendAct;
  int _ns = lookup[_i].ns;
  unsigned short _k = nondet_ushort();
  __CPROVER_assume((_k >= 0) && (_k < _ns));
  return (_sa[_k])(_i,1);
}

void Sync(int _j, int* _m) {
  for (int _i = 0;  _i < N; _i++)
    if (tgt[_i]) {
      tgt[_i] = 0;
      receive(_i,_j,_m);
    }
}

void receive(int _i, int _j, int* _m) {
  ptr* _ra = lookup[_i].RecvAct;
  int _nr = lookup[_i].nr;
  for (int _k = 0; _k < _nr; _k++)
    if ((_ra[_k])(_i,_j,_m)) break;
}

int schedule() {
  unsigned short _i = nondet_ushort();
  __CPROVER_assume((_i >= 0) && (_i < N));
  return _i;
}

int available() {
  int _i,_k,_ns;
  pts* _sa;
  for (_i = 0; _i < N; _i ++) {
    _ns = lookup[_i].ns;
    _sa = lookup[_i].SendAct;
    for (_k = 0; _k < _ns; _k++)
      if ((_sa[_k])(_i,0))
	return 1;
  }
  return 0;
}
\n".
