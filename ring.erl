-module(ring).
-export([start/4,spawnRing/4,menage/5]).

start(RingID,SvPid,StPid,Size)
  when is_pid(SvPid),  is_pid(StPid), Size > 0 
  -> spawn(?MODULE,spawnRing,[RingID,SvPid,StPid,Size]).


spawnRing(RingID,SvPid,StPid,Size) ->
   StPid ! {ring,start,RingID,Size,now()},
   Next = lists:foldr(
	    fun(N,Next) -> spawn(?MODULE,menage,[RingID,SvPid,StPid,N,Next]) end,
	    self(),lists:seq(1,Size)),
   SvPid ! {ring,created,RingID},
   StPid ! {ring,stop,RingID,now()},
   menage(RingID,SvPid,StPid,0,Next).


menage(RingID,SvPid,StPid,N,Next) when is_pid(Next) ->
   receive 
      stop when N > 0 -> Next ! stop;
      stop -> 
	 StPid ! io_lib:format("Destroying Ring #~w\n",[RingID]),
	 Next ! stop,
	 SvPid ! {ring,destroyed,RingID};

      {TokenID,undefined,StopTime} -> 
	 StPid ! io_lib:format("Token ~w recived on ring #~w on process #~w\n",[TokenID,RingID,N]),
	 case timer:now_diff(StopTime,now()) of
	    Diff when Diff > 0 ->
	       Next ! {TokenID,undefined,StopTime};
	    _  -> 
	       StPid ! {token,stop,TokenID,undefined,N,now()}
	 end,
	 menage(RingID,SvPid,StPid,N,Next);

      {TokenID,0,_} -> 
	 StPid ! io_lib:format("Token ~w recived on ring #~w on process #~w\n",[TokenID,RingID,N]),
	 StPid ! {token,stop,TokenID,0,N,now()},
	 menage(RingID,SvPid,StPid,N,Next);

      {TokenID,Steps,undefined} ->
	 StPid ! io_lib:format("Token ~w recived on ring #~w on process #~w\n",[TokenID,RingID,N]),
	 Next ! {TokenID,Steps-1,undefined},
	 menage(RingID,SvPid,StPid,N,Next);

      {TokenID,Steps,StopTime} -> 
	 StPid ! io_lib:format("Token ~w recived on ring #~w on process #~w\n",[TokenID,RingID,N]),
         case timer:now_diff(StopTime,now()) of	
            Diff when Diff > 0 ->
               Next ! {TokenID,Steps-1,StopTime};
            _  ->
               StPid ! {token,stop,TokenID,Steps,N,now()}
         end,  
         menage(RingID,SvPid,StPid,N,Next)
   end.

	 
	 


