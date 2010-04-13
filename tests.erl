-module(tests).
-export([test/0,test_start/0]).

-import(bench).
-import(stats).

test() ->
   {S,B} = test_start(),
   B ! {start,20},
   B ! {start,100},
   B ! list_rings,
   B ! {token,0,20,undefined},
   B ! {token,1,10,undefined},
   B ! lists_ring,
   {S,B}.

test_start() -> 
   S = stats:start(),
   {S,bench:start(S)}.
      
