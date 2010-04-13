-module(stats).
-export([start/0,menage/2]).

-record(token,{startTime,stopTime,steps,stepsDone,processNum}).
-record(ring,{startTime,stopTime,len}).

start() -> spawn(?MODULE,menage,[dict:new(),dict:new()]).

menage(Tokens,Rings) ->
   receive 

      stop -> io:format("PID: ~w, stats stoped\n",[self()]);

      {ring,start,RingID,Size,StartTime} ->
	 menage(Tokens,dict:store(  RingID  
				  , #ring{
				         startTime =  StartTime
				       , stopTime = stopTime
				       , len = Size 
				       }
				  , Rings
			       ));

      {ring,stop,RingID,StopTime} -> 
	Rings1 = case dict:find(RingID,Rings) of
		    {ok,Ring} -> dict:store(RingID,Ring#ring{stopTime = StopTime},Rings);
		    error -> 
		       io:format("PID ~w stats: error ring #~w doesnt exists\n",[self(),RingID]),
		       Rings
		 end,	       
	menage(Tokens,Rings1);


      {ring,report} -> 
	 dict:map(fun(RingID,Ring) -> 
		  lists:map(fun(F) -> apply(F,[RingID,Ring]) end,ringStats()) end,Rings),
	 menage(Tokens,Rings);

      {ring,reset} -> menage(Tokens,dict:new());

      {token,stop,TokenID,Steps,ProcessNum,StopTime} ->
	 %%io:format("wtf? Toknes: ~w\n",[dict:to_list(Tokens)]),
	 Tokens1 = case dict:find(TokenID,Tokens) of
		    {ok,Token} -> dict:store( TokenID
					    , Token#token{
							   stopTime = StopTime
							 , stepsDone = abs(ProcessNum - Steps)
							 , processNum = ProcessNum
							 }
					    ,Tokens
					    );
		    error -> 
		       io:format("PID ~w stats: error token #~w doesnt exists\n",[self(),TokenID]),
		       Tokens
		 end,
	  menage(Tokens1,Rings);

       {token,start,TokenID,Steps,CurrentTime} ->
	  Tokens1 = dict:store(	TokenID 
			      , #token{
				        startTime = CurrentTime
				      , steps = Steps
				      } 
			      , Tokens),
          %%io:format("token #~w, added,tokens ~w\n",[TokenID,dict:to_list(Tokens1)]),
	  menage(Tokens1,Rings);

       {token,report} ->
	  dict:map(fun(TokenID,Token) ->
		   lists:map(fun(F) -> apply(F,[TokenID,Token]) end,tokenStats()) end,Tokens),
	  menage(Tokens,Rings);

       {token,reset} -> menage(dict:new(),Rings);

       Msg -> 
	  io:format("PID ~w stats: ~s\n",[self(),Msg]),
	  menage(Rings,Tokens)
    end.



 tokenStats() -> [].
 ringStats() -> []. 

      
	




