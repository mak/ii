-module(slaveManage).
-export([start/1,start/2,stop/1,add_host/2,remove_host/2,choose_node/1]).
-export([init/1,handle_cast/2,handle_call/3,handle_info/2]).
-behavior(gen_server).

start(Name) ->
  case net_adm:host_file() of
     {error,Reason} -> error_logger:error_report(Reason);
     Hosts -> start(Name,Hosts)
  end.

start(Name,Hosts) ->
   case gen_server:start(?MODULE,Hosts,[]) of
      {ok,Pid} -> register(Name,Pid);
      {error,Error} -> error_logger:error_report(Error)
   end.

stop(Name) -> gen_server:call(Name,stop).
add_host(Name,Host) -> gen_server:cast(Name,{add_host,Host}).
remove_host(Name,Host) -> gen_server:call(Name,{remove_host,Host}).
choose_node(Name) -> gen_server:call(Name,choose_node).

init(Hosts) -> 
   net_kernel:monitor_nodes(true),
   {ok,lists:foldl( fun start_slave/2,  Hosts)}.

start_slave(H,D) -> 
   case slave:start_link(H) of
      {ok,Node} -> dict:store(H,Node,D);
      {error,R} -> error_logger:warning_report(R),D
   end.

handle_cast({add_host,Host},Hosts) -> {noreply,start_slave(Host,Hosts)}.

handle_call(stop,_,Hosts) -> {stop,normal,Hosts};
handle_call(choose_node,_,Hosts) -> {ok,min_node(Hosts),Hosts};
handle_call({remove_host,Host},_,Hosts) -> 
   case dict:find(Host,Hosts) of
      {ok,Val} -> slave:stop(Val), 
	 receive {nodedown,Val} -> {reply,ok,dict:erase(Host,Hosts)} end;
      error -> {reply,not_found,Hosts}
   end.

handle_info({nodeup,_},Hosts) -> {noreply,Hosts};
handle_info({nodedown,Node},Hosts) ->
   Host = lists:splitwith(fun(C) -> C =:= '@' end,atom_to_list(Node)),
   start_slave(Node,dict:erase(Host,Hosts)).

min_node(Hs) -> dict:fold(fun (_,H,Acc) -> min(H,Acc) end,{undef,undef},Hs).

min(H,{undef,undef}) -> {H,usage(H)};
min(H,{H1,U}) -> 
   case usage(H) of
      U1 when U1 >= U -> {H,U};
      U1 -> {H1,U1}
   end.

usage(Host) ->
   rpc:call(Host,application,start,[sasl],infinity),
   rpc:call(Host,application,start,[os_mon],infinity),
   case rpc:call(Host,cpu_sup,util,[],infinity) of
      {_,Reason} -> error_logger:error_report(Reason);
      U -> U
   end.



