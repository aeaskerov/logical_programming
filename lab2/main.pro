implement main
    open core, stdio, file

domains
    role = goalkeeper; defender; midfielder; forward.
    sum_goals = integer.

class facts - footballDB
    команда : (integer ID, string Stadium) nondeterm.
    стадион : (integer ID, string StadiumName, string City) nondeterm.
    занимает : (integer ID1, integer ID2) nondeterm.
    футболист : (integer ID, string Name, integer Age, integer TeamNumber, role Role) nondeterm.
    матч : (integer ID, string Date, integer HostID, integer GuestID, integer HostScore, integer GuestScore, integer StadiumID) nondeterm.

class facts
    s : (real Sum) single.

clauses
    s(0).

class predicates
    победил : (integer Id_game, string Winner) nondeterm anyflow.
clauses
    победил(Id_game, Winner) :-
        матч(Id_game, _, Id_host, _, Score1, Score2, _),
        Score1 > Score2,
        команда(Id_winner, Winner),
        Id_host = Id_winner.
    победил(Id_game, Winner) :-
        матч(Id_game, _, _, Id_guest, Score1, Score2, _),
        Score2 > Score1,
        команда(Id_winner, Winner),
        Id_guest = Id_winner.
        % победил(Id_game, Winner).

class predicates
    ничья : (integer Id_game) nondeterm anyflow.
clauses
    ничья(Id_game) :-
        матч(Id_game, _, _, _, Score1, Score2, _),
        Score2 = Score1.
        % ничья(Id_game).

class predicates
    общийгород : (string City1, string Team1, string Team2) nondeterm anyflow.
clauses
    общийгород(City1, Team1, Team2) :-
        стадион(Id_stadium1, _, City1),
        стадион(Id_stadium2, _, City2),
        City1 = City2,
        занимает(Id_stadium1, Id_team1),
        команда(Id_team1, Team1),
        занимает(Id_stadium2, Id_team2),
        команда(Id_team2, Team2),
        Id_team1 <> Id_team2.
        % общийгород("Мадрид", Team1, Team2).

class predicates
    общийстадион : (string Stadium, string Team1, string Team2) nondeterm anyflow.
clauses
    общийстадион(Stadium, Team1, Team2) :-
        занимает(Id_stadium1, Id_team1),
        занимает(Id_stadium2, Id_team2),
        Id_stadium1 = Id_stadium2,
        команда(Id_team1, Team1),
        команда(Id_team2, Team2),
        Id_team1 <> Id_team2,
        стадион(Id_stadium1, Stadium, _).
        % общийстадион("Джузеппе Меацца", Team1, Team2).

class predicates
    многозабито : (string Date, string Host, string Guest) nondeterm anyflow.
clauses
    многозабито(Date, Host, Guest) :-
        матч(_, Date, Id_host, Id_guest, Score1, Score2, _),
        Score1 + Score2 > 4,
        команда(Id_host, Host),
        команда(Id_guest, Guest).
        % многозабито(Date, Team1, Team2).

% младше20(Name, Age, Role).
class predicates
    младше20 : (string Name, integer Age, role Role) nondeterm anyflow.
clauses
    младше20(Name, Age, Role) :-
        футболист(_, Name, Age, _, Role),
        Age < 20.

class predicates
    всегоголов : (integer Id) nondeterm anyflow.
clauses
    всегоголов(Id) :-
        матч(Id, _, _, _, Score1, Score2, _),
        assert(s(0)),
        s(Sum),
        assert(s(Score1 + Score2)),
        fail.
    всегоголов(Id) :-
        матч(Id, _, _, _, Score1, Score2, _),
        s(Sum),
        writef("Голов за игру %: %", Id, Sum),
        nl.

% id_матча, дата_проведения, id_хозяев,
% id_гостей, счёт_хозяев, счёт_гостей, id_стадиона
/*
команда(10, "Бавария").                 % id_команды, команда
стадион(1, "Джузеппе Меацца", "Милан").         % id_стадиона, название_стадиона, город
занимает(1, 1).                     % id_стадиона, id_команды
футболист(44, "Маркус Рэшфорд", 26, 4, нападающий).   % id_игрока, имя_игрока, возраст, id_команды, роль
матч(15, "22.07.2023", 8, 9, 3, 1, 8). % id_матча, дата_проведения, id_хозяев, id_гостей, счёт_хозяев, счёт_гостей, id_стадиона
*/
clauses
    run() :-
        consult("../footballDB.txt", footballDB),
        fail.

    run() :-
        write("Победил\n"),
        победил(Id_game, Winner),
        write(Id_game),
        write(": "),
        write(Winner),
        nl,
        fail.

    run() :-
        write("Ничья\n"),
        ничья(Id_game),
        write(Id_game),
        nl,
        fail.

    run() :-
        write("Общий город\n"),
        общийгород("Мадрид", Team1, Team2),
        writef("Мадрид: % and %", Team1, Team2),
        nl,
        fail.

    run() :-
        write("Общий стадион\n"),
        общийстадион("Джузеппе Меацца", Team1, Team2),
        writef("%: % and %", "Джузеппе Меацца", Team1, Team2),
        nl,
        fail.

    run() :-
        write("Много забито\n"),
        многозабито(Date, Team1, Team2),
        writef("%: % and %", Date, Team1, Team2),
        nl,
        fail.

    run() :-
        write("Младше 20\n"),
        младше20(Name, Age, Role),
        writef("%, %, %", Name, Age, Role),
        nl,
        fail.

    run() :-
        write("Всего голов за матч\n"),
        всегоголов(8),
        nl,
        fail.

    run().

end implement main

goal
    console::runUtf8(main::run).
