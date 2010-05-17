-module(msort).
-export([parallel_merge_sort/3,split_many/2,msort_conc/2,loop/2]).

parallel_merge_sort([],PPN,L) ->
   L1 = split_many(erlang:round(length(L) / PPN),L),
   lists:foreach(fun(L2) -> spawn(?MODULE,msort_conc,[self(),L2]) end,L1),
   loop([],PPN);

parallel_merge_sort(Nodes,ProcPerNode,ListToSort) ->
   L = split_many(erlang:round(length(ListToSort) / length(Nodes)),ListToSort),
   collect(lists:map(fun({N,L1}) -> rpc:call(N,?MODULE,parallel_merge_sort,[[],ProcPerNode,L1]) end,
	 lists:zip(Nodes,L))).

collect(L) -> lists:foldl(fun(L1,S) -> merge(L1,S) end,[],L). 

merge([],L) -> L;
merge(L,[]) -> L;
merge([X|XS],[Y|YS]) when X >= Y -> [Y | merge([X|XS],YS)];
merge([X|XS],YS) -> [X|merge(XS,YS)].

split_many(N,L) when N >= length(L) -> [L];
split_many(N,L) -> 
   {L1,L2} = lists:split(N,L),
   [L1|split_many(N,L2)].

loop(L,0) -> collect(L);
loop(L,N) ->  receive  {join,L1} -> loop([L1|L],N-1)  end.

msort_conc(Par,L) -> Par ! {join,msort(L)}.
msort([X]) -> [X];
msort(XS) ->
   {L1,L2} = lists:split(length(XS) div 2,XS),
   merge(msort(L1),msort(L2)).

      
