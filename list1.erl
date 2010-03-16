-module(list1).
-export([imax/1,isum/1,rjust/2,ljust/2,center/2,mergesort/1,split/2,merge/2]).


imax([])  -> erlang:error("imax: empty list");
imax([H|T]) ->  foldl(fun(X,Y) -> max(X,Y) end,H,T).

isum([]) -> erlang:error("isum: empty list");
isum([H|T]) ->  foldl(fun(X,Y) -> plus(X,Y) end,H,T).


foldl(_,C,[]) -> C;
foldl(F,C,[H|T]) -> foldl(F,F(H,C),T).

max(X,Y) when is_integer(X) and  is_integer(Y) -> 
   if 
      X > Y -> X;
      true  -> Y
   end;
max(_,_) -> erlang:error("max: one of arguments isnt integer").

plus(X,Y) when is_integer(X) and is_integer(Y) -> X + Y;
plus(_,_) -> erlang:error("plus: one of arguments isnt integer").


replicate(_,0) -> [];
replicate(E,K) -> [E|replicate(E,K-1)].

ljust(S,W) when length(S) >=  W -> S;
ljust(S,W) -> replicate(" ",W-length(S)) ++ S.

rjust(S,W) when length(S) >= W -> S;
rjust(S,W) -> S ++ replicate(" ",W-length(S)).

center(S,W) when length(S) >= W -> S;
center(S,W) -> 
   R = replicate(" ",W-length(S)/2),
   R++ S ++ R.


merge([],L) -> L;
merge(L,[]) -> L;
merge([H|T],[H1|T1]) when is_integer(H) and is_integer(H1) ->
   if 
      H  > H1  -> [H1|merge([H|T],T1)];
      H =< H1  -> [H|merge(T,[H1|T1])]
   end;
merge(_,_) -> erlang:error("merge: one of heads isnt integer").

mergesort([]) -> [];
mergesort([X]) -> [X];
mergesort(L) -> 
  {L1,L2} = split(L,length(L) div 2),
  merge(mergesort(L1),mergesort(L2)).

split(L,N) -> split_acc(L,[],N).

split_acc(L1,L2,0) -> {rev(L2),L1};
split_acc([H|T], A, N) -> split_acc(T,[H|A],N-1).

rev(L) -> foldl(fun(X,Y) -> [X|Y] end,[],L).

