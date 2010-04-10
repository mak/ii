#!/usr/bin/env escript

%-module(zadanie2).
%-compile(export_all).

main([]) -> main(["50"]);
main([Width]) -> main([Width, "2"]);
main([Width, Indent]) -> loop(list_to_integer(Width),
                                list_to_integer(Indent)).

loop(Width, Indent) ->
    case get_paragraph() of
        eof -> ok;
        ""  -> loop(Width, Indent);
        Par -> 
            io:format("~s\n\n", [format_paragraph(Par, Width, Indent)]),
            loop(Width, Indent)
    end.

format_paragraph(Par, Width, Indent) -> 
    format(string:tokens(Par, " \n"), Width, Indent, []).

format([], _, _, Lines) -> string:join(lists:reverse(Lines), "\n");

format(Words, Width, Indent, []) ->
    {Line, Rest} = make_line(Words, Width - Indent),
    Indented = lists:duplicate(Indent, 32) ++ Line,
    format(Rest, Width, 0, [Indented]);

format(Words, Width, _, Lines) ->
    case make_line(Words, Width) of
        {"", _} -> Lines;
        {Line, Rest} -> format(Rest, Width, 0, [Line|Lines])
    end.

make_line(Words, Width) ->
    case take_words(Words, Width) of
        {Taken, []}   -> {string:join(Taken, " "), []};
        {Taken, Rest} -> {fill_to_width(Taken, Width), Rest}
    end.

fill_to_width([], _) -> "";
fill_to_width([Word], _) -> Word;
fill_to_width([Word|Words], Width) -> 
    WordsWidth = lists:foldl(fun(S, X) -> 
                X + length(S) end, length(Word), Words),
    N = (Width - WordsWidth) div (length(Words)),
    case (Width - WordsWidth) rem (length(Words)) of
        0 -> string:join([Word|Words], lists:duplicate(N, 32));
        M when M > 0 -> join([Word|Words], N, M)
    end.

join([], _, _) -> "";

join(Words, N, 0) ->
    string:join(Words, lists:duplicate(N, $ ));

join([Word|Words], N, M) when M > 0 ->
    Word ++ lists:duplicate(N + 1, $ ) ++ join(Words, N, M - 1).

take_words(Words, Width) ->
    take_words(Words, Width, []).

take_words([Word|Words], Width, []) when length(Word) > Width ->
    {[Word], Words};

take_words([Word|Words], Width, Taken) when length(Word) =< Width ->
    take_words(Words, Width - length(Word) - 1, [Word|Taken]);

take_words(Words, _, Taken) -> {lists:reverse(Taken), Words}.

get_line() ->
    case io:get_line("") of
        eof -> eof;
        Line -> string:strip(string:strip(Line, both, 10), both)
    end.

get_paragraph() -> 
    case get_line() of
        eof -> eof;
        Line -> get_paragraph(Line)
    end.

get_paragraph(Par) -> 
    case get_line() of
        eof -> Par;
        "" -> Par;
        Line -> get_paragraph(string:concat(Par, Line))
    end.
