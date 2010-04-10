#!/usr/bin/env escript

-module(zadanie1).
-compile(export_all).

-record(ip_header, {version = 4, header_length = 5, tos,
                total_length = 576, identification, flags = 0, ttl, 
                protocol, checksum, src, dst, additional, data}).

main([]) ->
    loop().

loop() -> 
    IP = read_ip_packet(),
    print_ip_header(IP).

ip_to_string(IP = [_, _, _, _]) ->
    string:join(lists:map(fun erlang:integer_to_list/1, IP), ".").

hex_digit(N) when (N >= 0) and (N =< 9) -> integer_to_list(N);
hex_digit(10) -> "A";
hex_digit(11) -> "B";
hex_digit(12) -> "C";
hex_digit(13) -> "D";
hex_digit(14) -> "E";
hex_digit(15) -> "F".


byte_to_hex(N) when (N >= 0) and (N =< 255) ->
    A = N div 16,
    B = N rem 16,
    hex_digit(A) ++ hex_digit(B).


bytes_to_hex(Bytes) ->
    string:join(lists:map(fun(X) -> byte_to_hex(X) end, Bytes), " ").


print_data(Bytes) -> 
    io:format("\n~s\n", [bytes_to_hex(Bytes)]).


print_ip_header(IP) when is_record(IP, ip_header) ->
    
    Version = case (IP#ip_header.version) of
            4 -> "IPv4";
            6 -> "IPv6"
        end,
    
    Dst = ip_to_string(IP#ip_header.dst),
    Src = ip_to_string(IP#ip_header.src),

    Protocol = case IP#ip_header.protocol of
            tcp -> "TCP";
            udp -> "UDP";
            icmp -> "ICMP"
       end,

    PrettyIP = IP#ip_header{version = Version, src = Src, 
                    protocol = Protocol, dst = Dst},

    io:format("IP Header\n-------------------\n"
               "Version: ~s\n"
               "Header Length: ~w words\n"
               "Type of Service: ~w\n"
               "Total Length: ~w\n"
               "Identification: ~w\n"
               "Flags: ~w\n"
               "TTL: ~w\n"
               "Protocol: ~s\n"
               "Checksum: ~w\n"
               "Src: ~s\n"
               "Dst: ~s\n"
               "Additional: ~w\n~i\n",
               tl(tuple_to_list(PrettyIP))),

    case IP#ip_header.protocol of
        tcp -> print_tcp_packet(IP#ip_header.data);
        udp -> print_udp_packet(IP#ip_header.data);
        icmp-> print_icmp_packet(IP#ip_header.data);
        raw_data -> print_data(IP#ip_header.data)
    end.


sum_16_bit([]) -> 0;
sum_16_bit([A, B|Rest]) ->
	bytes_to_integer([A, B]) + sum_16_bit(Rest).


read_ip_packet() ->
	Bytes = read_bytes(12),
    Header = bytes_to_integer(Bytes),
	<<Version:4, HeaderLength:4, ToS:8, TotalLength:16, Identification:16, 
	Flags:16, TTL:8, P:8, Checksum:16>> = <<Header:96>>,

    Protocol = case P of
        1 -> icmp;
        6 -> tcp;
        17 -> udp;
        true -> raw_data
    end,
	
	SrcIP = read_bytes(4),
    [B1, B2, B3, B4] = SrcIP,
	DestIP = read_bytes(4),
	[B5, B6, B7, B8] = DestIP,


	C = sum_16_bit(Bytes) + bytes_to_integer([B1, B2]) +
		bytes_to_integer([B3, B4]) + bytes_to_integer([B5, B6]) +
		bytes_to_integer([B7, B8]),

	<<Tmp:16>> = <<C:16>>,
    
	C2 = C div 65536 + Tmp,

	io:format("C: ~w\nTmp: ~w\nC2: ~w\n", [C, Tmp, C2]),
	C3 = C2 + C2 div 65536,

	io:format("My checksum: ~w\n", [65535 - C3]),

    Additional = read_bytes(4 * HeaderLength - 20),
    Data = case Protocol of 
        tcp -> read_tcp_packet(TotalLength - 4 * HeaderLength);
        udp -> read_udp_packet();
        icmp -> read_icmp_packet();
        true -> read_bytes(TotalLength - 4 * HeaderLength)
    end,
        
    {ip_header, Version, HeaderLength, ToS, TotalLength, Identification, Flags,
     TTL, Protocol, Checksum, SrcIP, DestIP, Additional, Data}.
   

read_udp_packet() ->
    Header = bytes_to_integer(read_bytes(8)),
    <<SrcPort:16, DstPort:16, Length:16, Checksum:16>> = <<Header:64>>,
    Data = read_bytes(Length - 8),
    {SrcPort, DstPort, Length, Checksum, Data}.


print_udp_packet({SrcPort, DstPort, Length, Checksum, Data}) ->
    io:format("UDP Header:\n--------------------\n"
              "Source port: ~w\n"
              "Destination port: ~w\n"
              "Length: ~w\n"
              "Checksum: ~w\n",
              [SrcPort, DstPort, Length, Checksum]),
    print_data(Data).


read_icmp_packet() -> 
	Header = bytes_to_integer(read_bytes(8)),
	<<Type:8, Code:8, Checksum:16, ID:16, Sequence:16>> = <<Header:64>>,
    {Type, Code, Checksum, ID, Sequence}.


print_icmp_packet(Packet) ->
    io:format("ICMP Header:\n------------------\n"
              "Type: ~w\n"
              "Code: ~w\n"
              "Checksum: ~w\n"
              "ID: ~w\n"
              "Sequence: ~w\n",
              tuple_to_list(Packet)).


tcp_flags_to_string(Flags) ->
    <<CWR:1, ECE:1, URG:1, ACK:1, PSH:1, RST:1, 
        SYN:1, FIN:1>> = <<Flags:8>>,

    L = [{CWR, "CWR"}, {ECE, "ECE"}, {URG, "URG"}, {ACK, "ACK"}, 
        {PSH, "PSH"}, {RST, "RST"}, {SYN, "SYN"}, {FIN, "FIN"}],

    L2 = lists:filter(fun({A, _}) -> A == 1 end, L),

    string:join(lists:map(fun({_, B}) -> B end, L2), " ").


read_tcp_packet(Length) ->
	Header = bytes_to_integer(read_bytes(20)),
	<<SrcPort:16, DstPort:16, SeqNum:32, AckNum:32, Offset:4, Reserved:4, 
	  Flags:8, WindowSize:16, Checksum:16, UrgentPointer:16>> = <<Header:160>>,
    Additional = bytes_to_hex(read_bytes(Offset * 4 - 20)),
    Data = read_bytes(Length - Offset * 4),
    [Data, SrcPort, DstPort, SeqNum, AckNum, Offset, Reserved, 
        tcp_flags_to_string(Flags), WindowSize, Checksum, 
        UrgentPointer, Additional].


print_tcp_packet([Data|Packet]) ->
    io:format("TCP Header:\n--------------------\n"
              "Source port: ~w\n"
              "Destination port: ~w\n"
              "Sequence number: ~w\n"
              "Acknowledgment number: ~w\n"
              "Offset: ~w\n"
              "Reserved: ~w\n"
              "Flags: ~s\n"
              "Window size: ~w\n"
              "Checksum: ~w\n"
              "Urgent pointer: ~w\n"
              "Additional: ~s\n",
              Packet),

     print_data(Data).


is_hex_digit(D) ->
    (D >= "0") and (D =< "9")
    or
    (D >= "a") and (D =< "f")
    or
    (D >= "A") and (D =< "F").


hex_to_integer("a") -> 10;
hex_to_integer("b") -> 11;
hex_to_integer("c") -> 12;
hex_to_integer("d") -> 13;
hex_to_integer("e") -> 14;
hex_to_integer("f") -> 15;
hex_to_integer("A") -> 10;
hex_to_integer("B") -> 11;
hex_to_integer("C") -> 12;
hex_to_integer("D") -> 13;
hex_to_integer("E") -> 14;
hex_to_integer("F") -> 15;
hex_to_integer([N]) -> [Zero] = "0", N - Zero.

read_bytes(0) -> [];
read_bytes(N) when N > 0 ->
    case io:fread("", "~c~c") of
        {ok, Chars} ->
            case lists:all(fun(D) -> is_hex_digit(D) end, Chars) of
                true  -> 
                    [A, B] = Chars,
                    Byte = hex_to_integer(A)*16 + hex_to_integer(B),
                    [Byte | read_bytes(N - 1)];
                false -> input_error
            end;
        eof -> []
    end.
   
bytes_to_integer(Bytes) -> 
    lists:foldl(fun(X, A) -> 256 * A + X end, 0, Bytes).
