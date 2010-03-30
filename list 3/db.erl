-module(db).
-compile(export_all).

-record(db, {type, data = []}).

create(Record) -> {ok, #db{type = Record}}.


insert(DB = #db{data = []}, Row) ->
    {DB#db{data = [{1, Row}]}, 1};


insert(DB = #db{data = [Rest = {Id, _} | _]}, Row) ->
    {DB#db{data = [{Id + 1, Row}|Rest]}, Id + 1}.


select(DB, Pred) -> 
    try
        {ok, lists:filter(fun({_, Row}) -> Pred(Row) end, DB#db.data)}
    catch
        _:_ -> {error, bad_query}
    end.


select(DB, Pred, Field) ->
    try
        {ok, lists:filter(fun({_, Row}) -> Pred(element(Field,Row)) end, 
                DB#db.data)}
    catch
        _:_ -> {error, bad_query}
    end.


delete(DB, Pred) ->
    try
        DbPred = fun({_, Row}) -> Pred(Row) end,
        {Deleted, Remained} = lists:partition(DbPred, DB#db.data),
        {ok, DB#db{data = Remained}, Deleted}
    catch
        _:_ -> {error, wrong_query}
    end.

map_pred([], _, _) -> [];
map_pred([L|LS], Pred, F) ->
    case Pred(L) of
        true -> [F(L)|map_pred(LS, Pred, F)];
        false -> [L|map_pred(LS, Pred, F)]
    end.

update(DB, Pred, Func) ->
    try
        DbPred = fun({Id, Row}) -> 
                    case Pred(Row) of
                        true -> {Id, Func(Row)};
                        false -> {Id, Row}
                    end
                 end,
        Updated = lists:filter(fun({_, Row}) -> Pred(Row) end, 
            DB#db.data),
        NewData = lists:map(DbPred, DB#db.data),
        {ok, DB#db{data = NewData}, Updated}
    catch
        _:_ -> {error, wrong_query}
    end.


update(DB, Pred, Func, Field) ->
    try
        DbPred = fun({Id, Row}) -> 
                case Pred(element(Field, Row)) of
                        true -> {Id, Func(element(Field, Row))};
                        false -> {Id, Row}
                    end
                 end,
                 Updated = lists:filter(fun({_, Row}) -> Pred(element(Field, Row)) end, 
            DB#db.data),
        NewData = lists:map(DbPred, DB#db.data),
        {ok, DB#db{data = NewData}, Updated}
    catch
        _:_ -> {error, wrong_query}
    end.
