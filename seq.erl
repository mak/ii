#!/usr/bin/env escript

main(ARGS) -> 
   L = case map(fun(X) ->  list_to_integer(X) end,ARGS) of
	[N] -> seq(1,1,N);
	[N,M] -> seq(N,1,M);
	[N,K,M] -> seq(N,M,K)
       end,
   io:format("~w~n",[L]).


seq(N,K,M) -> seq_acc(N,K,M,[]).

seq_acc(N,_,M,L) when N > M -> reverse(L);
seq_acc(N,K,M,L) -> seq_acc(N+K,K,M,[N|L]).

map(_,[]) -> [];
map(F,[H|T]) -> [F(H)|map(F,T)].

reverse(L) -> rev_acc(L,[]).
rev_acc([],A) -> A;
rev_acc([H|T],L) -> rev_acc(T,[H|L]).
