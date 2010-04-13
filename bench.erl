-module(bench).
-export([start/1,menage/4]).

-import(stats).
-import(ring).


start(StPid) -> spawn(?MODULE,menage,[StPid,dict:new(),0,0]).

menage(StPid,Rings,CRingID,CTokenID) ->
   receive 

      {start,Size} ->
	 NewRing = ring:start(CRingID,self(),StPid,Size),
	 receive 
	    {ring,created,RingID} ->
	       StPid ! io_lib:format("Ring #~w created, size ~w",[RingID,Size]),
	       Rings1 = dict:store(RingID,NewRing,Rings),
	       menage(StPid,Rings1,RingID+1,CTokenID)
	 end;

      {stop,RingID} ->
	 R1 = case dict:find(RingID,Rings) of
		{ok,Ring} -> 
		  Ring ! stop,
		  receive 
		    {ring,destroyed,RingID} ->
		      StPid ! io_lib:format("Ring #~w destroyed",[RingID])
		  end,
		  dict:erase(RingID,Rings);
		error ->
		  StPid ! io_lib:format("Svisor(~w): ring #~w doesnt exists",[self(),RingID]),
		  Rings
	 end,
	 menage(StPid,R1,CRingID,CTokenID);

      {token,RingID,Steps,undefined} ->
	 case dict:find(RingID,Rings) of
	    {ok,Ring} -> 
	       StPid ! {token,start,CTokenID,Steps,now()},
	       Ring ! {CTokenID,Steps,undefined};
	    error -> StPid ! io_lib:format("Svisor(~w): ring #~w doesnt exists",[self(),RingID])
	 end,
	 menage(StPid,Rings,CRingID,CTokenID+1);
%% TimeToStop -> secunds
      {token,RingID,Steps,TimeToStop} ->
           case dict:find(RingID, Rings) of
                     {ok, Ring} ->
	                      {MegaSec, Sec, Milisec} = now(),
	                          StopTime = {MegaSec + ((Sec + TimeToStop) div 1000000),
	                               (Sec + TimeToStop) rem 1000000, Milisec},
			      StPid ! {token,start,CTokenID,Steps,now()},
			      Ring ! {CTokenID, Steps, StopTime};
		     error ->  StPid ! io_lib:format("Svisor(~w): ring #~w doesnt exists",[self(),RingID])
            end,
            menage(StPid, Rings,CRingID,CTokenID+1);
      
      list_rings ->
	 StPid ! io_lib:format("Svisor(~w): Rings ~w",[self(),dict:to_list(Rings)]),
	 menage(StPid, Rings,CRingID,CTokenID);

      stop ->  
	 dict:map(fun(_,R) -> R ! stop end,Rings),
	 StPid ! io_lib:format("Svisor(~w): Rings destroyed, Svisor destroyed",[self()])
   end.

	 


