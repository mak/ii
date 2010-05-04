-module(mig_dict).
-export([migrate/1,eval/2,start/0]).
%% -behavior(gen_server).


start() -> global:register_name(mdict,spawn(fun () -> loop(dict:new()) end )).

eval(Fun,Args) -> global:send(mdict,{eval,self(),Fun,Args}).
migrate(Node) -> global:send(mdict,{migrate,Node}).

migrate_beg(Node,Dict) ->
   case rpc:call(Node,?MODULE,start_mig,[Dict],infinity) of
      {_,Reason} -> error_logger:error_report(Reason);
      ok -> receive 
	    {global_name_conflict,Pid2,_} -> 
	       lists:foreach(fun(Msg) -> Pid2 ! Msg end, erlang:process_info(self(),messages)),
	       exit(normal) ;
	    Msg -> self() ! Msg
	 end
   end.

start_mig(Dict) ->
   process_flag(trap_exit,true),
   global:register_name(mdict,self(),fun global:notify_all_name/3 ),
   pre_loop(Dict).

pre_loop(Dict) -> 
   receive   
      {'EXIT',_,normal} -> process_flag(trap_exit,false), loop(Dict);
      Msg -> self() ! Msg,pre_loop(Dict)
   end.


loop(Dict) ->
   receive 
      {eval,R,F,Args} -> 
	 D = apply(dict,F,Args),
	 R ! {reply,D},
	 case catch dict:size(D) of
	    {_,{function_clause,_}} -> loop(Dict);
	    _ -> loop(D)
	 end;
      {migrate,Node} -> migrate_beg(Node,Dict)
   end.











