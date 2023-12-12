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

class predicates  %Вспомогательные предикаты
    длина : (A*) -> integer N.
    сумма_элем : (real* List) -> real Sum.
    среднее_списка : (real* List) -> real Average determ.

clauses
    длина([]) = 0.
    длина([_ | T]) = длина(T) + 1.

    сумма_элем([]) = 0.
    сумма_элем([H | T]) = сумма_элем(T) + H.

    среднее_списка(L) = сумма_элем(L) / длина(L) :-
        длина(L) > 0.

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

% Лабораторная работа №3
class predicates
    участникикоманды : (string TeamName) -> string* Footballers determ.
clauses
    участникикоманды(TeamName) = List :-
        команда(IDTeam, TeamName),
        !,
        List = [ FootballerName || футболист(_, FootballerName, _, IDTeam, _) ].

class predicates
    командыСыгравшиеЗаДень : (string Date) -> string* Teams determ.
clauses
    командыСыгравшиеЗаДень(Date) = List :-
        матч(_, Date, HostID, GuestID, _, _, _),
        !,
        List =
            [ TeamName ||
                команда(IDTeam, TeamName),
                матч(_, Date, HostID, GuestID, _, _, _),
                IDTeam = HostID
                or
                команда(IDTeam, TeamName),
                матч(_, Date, HostID, GuestID, _, _, _),
                IDTeam = GuestID
            ].

class predicates
    средВозраст : (string Team) -> real N determ.
clauses
    средВозраст(Team) =
        среднее_списка(
            [ Age ||
                команда(IDTeam, Team),
                футболист(_, _, Age, IDTeam, _)
            ]).

class predicates
    колвоИгроковКоманды : (string Team) -> integer N determ.
clauses
    колвоИгроковКоманды(Team) = длина(участникикоманды(Team)).

class predicates
    write_string : (string* Строки).
clauses
    write_string(L) :-
        foreach Элемент = list::getMember_nd(L) do
            write(Элемент, '; ')
        end foreach,
        write('\n').

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

    run() :-
        write("Участники команды Бавария:\n"),
        L = участникикоманды("Бавария"),
        write_string(L),
        fail.

    run() :-
        write("Средний возраст в команде Атлетико:\n"),
        AvgAge = средВозраст("Атлетико"),
        write(AvgAge),
        nl,
        fail.

    run() :-
        write("Количество игроков команды Бавария:\n"),
        Kolvo = колвоИгроковКоманды("Бавария"),
        write(Kolvo),
        nl,
        fail.

    run() :-
        write("Команды сыгравшие за 09.07.2023:\n"),
        L = командыСыгравшиеЗаДень("09.07.2023"),
        write_string(L),
        fail.

    run().

end implement main

goal
    console::runUtf8(main::run).
