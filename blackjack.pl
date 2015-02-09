:- use_module(library(lists), [nth0/3]).
:- use_module(library(random), [random/3]).
:- dynamic karta/2, novac/1, kartaURukama/3, naPotezu/1, ulog/1, ukupniUlog/1, dupliranaGrupa/1, grupe/2, ukupnoGrupa/1, trenutnaGrupa/1, prvaKartaDealera/1, blackjack/0.
:- retractall(novac(_)), assert(novac(1000)).
:- retractall(naPotezu(_)).
:- retractall(ulog(_)).
:- retractall(ukupniUlog(_)).

%karte za igru. 6 špilova
promijesajKarte :-
    retractall(karta(_,_)),
    assert(karta('A', 24)),
    assert(karta(2, 24)),
    assert(karta(3, 24)),
    assert(karta(4, 24)),
    assert(karta(5, 24)),
    assert(karta(6, 24)),
    assert(karta(7, 24)),
    assert(karta(8, 24)),
    assert(karta(9, 24)),
    assert(karta(10, 24)),
    assert(karta('J', 24)),
    assert(karta('Q', 24)),
    assert(karta('K', 24)).
    
:- retractall(karta(_,_)), promijesajKarte.

naPotezu('I').
ulog(0).
    
%************************************************************
%Pomoæni predikati

sumaListe([], 0).
sumaListe([H|T], S) :-
    sumaListe(T, S1),
    S is S1 + H.
    
% zbraja sve karte u igraèevim rukama. Najprije Aseve pretvara u 11-ice, a JQK u 10
zbrojKarata([], 0).
zbrojKarata([H|T], Z) :-
    zbrojKarata(T, Z1),
    (H == 'A' -> Z is Z1 + 11 ;
    (
       ((H == 'J' ; H == 'Q' ; H == 'K') -> Z is Z1 + 10 ;
           Z is Z1 + H
       )
    )).
    
    
brojDobivenihDupliranihGrupa(N) :-
    findall(X, (grupe(X,w), dupliranaGrupa(X)), L),
    length(L, N).

brojDobivenihNedupliranihGrupa(N) :-
    findall(X, (grupe(X,w), not(dupliranaGrupa(X))), L),
    length(L, N).
    
brojPushanihDupliranihGrupa(N) :-
    findall(X, (grupe(X,p), dupliranaGrupa(X)), L),
    length(L, N).
    
brojPushanihNedupliranihGrupa(N) :-
    findall(X, (grupe(X,p), not(dupliranaGrupa(X))), L),
    length(L, N).
    
    
imaDvijeJednakeKarte :-
    trenutnaGrupa(G),
    findall(X, kartaURukama('I', X, G), L),
    nth0(0, L, K1), nth0(1, L, K2),
    (K1 == K2; K1 == 'A', K2 == 1; K1 == 1, K2 == 'A').
    
    
svigrupePreko21 :-
    zbrojiKarte(Z1, 'I', 1), zbrojiKarte(Z2, 'I', 2),
    zbrojiKarte(Z3, 'I', 3), zbrojiKarte(Z4, 'I', 4),
    Z1 > 21, Z2 > 21, Z3 > 21, Z4 > 21.
    
    
postaviIshodGrupe(Grupa, Ishod) :-
    retract(grupe(Grupa, _)),
    assert(grupe(Grupa, Ishod)).
    
%************************************************************

% mijenjaIgracaNaPotezu
promijeniIgracaNaPotezu :-
    retract(naPotezu(I)),
    (I == 'I' -> assert(naPotezu('D')); assert(naPotezu('I'))).
    
% ovaj predikat inicijalizira igru za novo dijeljenje
pripremiIgru :-
    retractall(kartaURukama(_,_,_)),  % argumenti: igraè (dealer ili drugi igraè), karta, grupa. Treæi argument (grupa) predstavlja grupu u koju æe karta biti premještena jednom kada se par karti split-a
    retractall(dupliranaGrupa(_)),
    retractall(grupe(_,_)),
    retractall(ukupnoGrupa(_)),
    retractall(trenutnaGrupa(_)),
    retractall(ukupniUlog(_)),
    retractall(prvaKartaDealera(_)),
    retractall(blackjack),
    assert(grupe(1, u)),  % predstavlja sve grupe koje igraè ima (s pripadajuæim indeksima). Drugi argument može biti: w (win - pobjeda u toj grupi nad dealerom), l (lose - gubitak u toj grupi nad dealerom), p (push - ni pobjeda ni poraz u toj grupi nad dealerom, jednak broj karti), u (unknown - pobjeda ili poraz još nisu poznati)
    assert(trenutnaGrupa(1)),
    assert(ukupnoGrupa(1)),
    assert(ukupniUlog(0)).

% daje jednu random kartu iz špila. U obzir ulaze samo one karte koje POSTOJE još u špilu
randomKarta(Karta) :-
    random(0, 13, Rnd),
    nth0(Rnd, ['A', 2, 3, 4, 5, 6, 7, 8, 9, 10, 'J', 'Q', 'K'], K),
    karta(K, N),
    (N =:= 0 -> (!, randomKarta(Karta)) ; Karta = K).
                   
                   
% izvlaèi kartu iz špila i smanjuje broj te vrste karte u špilu.
izvuciKartu(Karta) :-
    randomKarta(Karta),
    retract(karta(Karta, N)),
    N1 is N - 1,
    assert(karta(Karta, N1)).


% vraæa ukupan broj karti tako da pretvara sve èinjenice karte u listu i zbraja ih
ukupanBrojKarti(N) :-
    findall(X, karta(_, X), L), !,
    sumaListe(L, N).
    
    
% vraæa broj karti u rukama nekog igraèa
brojKartiURukama(I, Broj, Grupa) :-
    findall(K, kartaURukama(I, K, Grupa), L),
    length(L, Broj).
    
% vraæa true, ako igraè može splitati. A to je: ako ima dvije iste karte i ako je splitao veæ manje od 3 puta (odnosno ako postoji ukupno manje od 4 grupe)
mozesplitati :-
    trenutnaGrupa(G),
    brojKartiURukama('I', 2, G),
    imaDvijeJednakeKarte,
    ukupnoGrupa(U), U < 4.


% uzima novac od igraèa
uzmiNovac(X) :-
    retract(novac(Novac)), Novac2 is Novac - X,
    assert(novac(Novac2)),
    retract(ukupniUlog(U)),
    U1 is U + X, assert(ukupniUlog(U1)).
    
% predikat za unos poèetnog uloga
unesiUlog :-
    write('Unesite ulog: '), read(X),
    novac(Novac), X =< Novac,
    uzmiNovac(X),
    retractall(ulog(_)), assert(ulog(X)).
    
unesiUlog :-
    write('Unesite ulog: '), read(X),
    novac(Novac), X > Novac,
    write('Prevelik iznos unesen! Imate '), write(Novac), write(' kn.'), nl,
    !, unesiUlog.
    

    
% I predstavlja igraèa, a D dealera
podijeliKarte(D2) :-
    izvuciKartu(I1), izvuciKartu(D1), izvuciKartu(I2), izvuciKartu(D2),
    assert(kartaURukama('I', I1, 1)), assert(kartaURukama('D', D1, 1)), assert(kartaURukama('I', I2, 1)), assert(kartaURukama('D', D2, 1)),
    assert(prvaKartaDealera(D1)),
    writeln('Novo dijeljenje. Karte:'),
    write('Dealer: '), write(D1), write(' '), write('X'), nl,
    write('Igrac: '), write(I1), write(' '), write(I2), nl.


% uzima kartu iz špila i dodaje ju igraèu u ruke
uzmiKartu(Karta) :-
    naPotezu(I),
    izvuciKartu(Karta), trenutnaGrupa(G),
    assert(kartaURukama(I, Karta, G)).
   

% zbraja karte odreðenog igraèa. Najprije zbraja sve Aseve kao jedanaestice, a ako ukupna vrijednost preðe 21, tada jedan po jedan as (koliko je potrebno mijenja u jedinice)
zbrojiKarte(Z, I, Grupa) :-
    findall(K, kartaURukama(I,K,Grupa), L),
    zbrojKarata(L, Z1),
    (Z1 > 21 ->
    (
       kartaURukama(I, 'A', Grupa) -> (retract(kartaURukama(I, 'A', Grupa)), assert(kartaURukama(I, 1, Grupa)), !, zbrojiKarte(Z, I, Grupa)); (Z is Z1)
    ); Z is Z1).
    

% ako je igraè dobio blackjack odmah s prve dvije karte. U tom sluèaju kasino plaæa u omjeru 3:2
isplatiIgracaZaBlackjackWin :-
    writeln('WIN!'),
    novac(NovacIgraca), ulog(UlogIgraca), NovaVrijednostNovca is NovacIgraca + 1.5 * UlogIgraca,
    retract(novac(_)), assert(novac(NovaVrijednostNovca)), assert(blackjack).
    
% Ako su i igraè i dealer dobili blackjack odmah s prve dvije karte, to je push i igraèu se vraæa novac
isplatiIgracaZaBlackjackPush :-
    writeln('PUSH'),
    novac(NovacIgraca), ulog(UlogIgraca), NovaVrijednostNovca is NovacIgraca + UlogIgraca,
    retract(novac(_)), assert(novac(NovaVrijednostNovca)), assert(blackjack).

% daje igraèu novac, s obzirom na broj dobivenih grupa, broj dobivenih dupliranih grupa i broj push-anih grupa
isplatiIgracuNovac(Dobiveno) :-
    novac(Novac), ulog(Ulog),
    brojDobivenihDupliranihGrupa(N1),
    brojDobivenihNedupliranihGrupa(N2),
    brojPushanihDupliranihGrupa(N3),
    brojPushanihNedupliranihGrupa(N4),
    Dobiveno is 4 * N1 * Ulog + 2 * (N2 + N3) * Ulog + N4 * Ulog,
    NovaVrijednostNovca is Novac + Dobiveno,
    retract(novac(_)), assert(novac(NovaVrijednostNovca)).



dupliraj(X) :-
    assert(dupliranaGrupa(X)).

% ovaj predikat uzima drugu kartu i stavlja je u novu grupu. Nakon toga u staru grupu dodaje još jednu kartu i ispisuje koja je to.
splitaj :-
    trenutnaGrupa(G),
    findall(X, kartaURukama('I', X, G), L),
    nth1(2, L, K),
    retract(kartaURukama('I', K, G)),
    NovaPozicija is G + 1,
    assert(kartaURukama('I', K, NovaPozicija)),
    assert(grupe(NovaPozicija, u)),
    uzmiKartu(Karta), write('Nova karta: '), write(Karta), write(', Grupa: '), write(G), nl.
    
% ako se radi o posljednjoj grupi igraèa, zaustavljamo igru, i dalje nastavlja dealer
sljedecaGrupa :-
    trenutnaGrupa(G), ukupnoGrupa(G).

% ako se ne radi o posljednjoj grupi igraèa, poveæavamo trenutnu grupu i zahtijevamo unos igraèa za sljedeæu grupu
sljedecaGrupa :-
    trenutnaGrupa(T), ukupnoGrupa(U),
    T < U, T1 is T + 1,
    retract(trenutnaGrupa(_)), assert(trenutnaGrupa(T1)), !,
    (naPotezu('I') -> ( writeln('Sljedeca grupa'), poteziIgraca('I') ); izvrsiPotezDealera ).


% kada dealer krene igrati, morat æe svoju ruku usporeðivati sa svim svojim kartama. Stoga je prije toga potrebno postaviti trenutnu grupu igraèa na 1
postaviNaPrvuGrupu :-
    retractall(trenutnaGrupa(_)),
    assert(trenutnaGrupa(1)).


% dealer æe stalno koristiti hit, sve dok je njegov zbroj na kartama manji od 17.
% ako se dealer odluèi za "hit" (samo u sluèaju kad ima zbroj svojih karti manji od 17)
izvrsiPotezDealera :-
    zbrojiKarte(Z, 'D', 1), Z < 17,
    uzmiKartu(Karta), writeln(Karta), !,
    izvrsiPotezDealera.

% ako se dealer odluèi za "stand", tada se zbrajaju karte od oba igraèa.
% Ako je dealer prešao 21
izvrsiPotezDealera :-
    zbrojiKarte(Z, 'D', 1), Z > 21,
    writeln('WIN!'),
    trenutnaGrupa(G),
    postaviIshodGrupe(G, w), !,
    sljedecaGrupa.
    
% Ako se dealer odluèi za "stand" i ako je igraè prešao 21
izvrsiPotezDealera :-
    trenutnaGrupa(G),
    zbrojiKarte(ZbrojDealera, 'D', 1), ZbrojDealera >= 17, ZbrojDealera =< 21, zbrojiKarte(ZbrojIgraca, 'I', G),
    ZbrojIgraca > 21, !,
    sljedecaGrupa.
    
% Ako je igraè pobijedio
izvrsiPotezDealera :-
    trenutnaGrupa(G),
    zbrojiKarte(ZbrojDealera, 'D', 1), ZbrojDealera >= 17, ZbrojDealera =< 21, zbrojiKarte(ZbrojIgraca, 'I', G),
    ZbrojIgraca > ZbrojDealera,
    writeln('WIN!'),
    postaviIshodGrupe(G, w), !,
    sljedecaGrupa.

% Ako se dealer odluèi za "stand" i ako dealer i drugi igraè imaju jednak zbroj karti
izvrsiPotezDealera :-
    trenutnaGrupa(G),
    zbrojiKarte(Zbroj, 'D', 1), Zbroj >= 17, Zbroj =< 21, zbrojiKarte(Zbroj, 'I', G),
    writeln('PUSH!'),
    postaviIshodGrupe(G, p), !,
    sljedecaGrupa.

% Ako se dealer odluèi za "stand" i ako je igraè izgubio
izvrsiPotezDealera :-
    trenutnaGrupa(G),
    zbrojiKarte(ZbrojDealera, 'D', 1), ZbrojDealera >= 17, ZbrojDealera =< 21, zbrojiKarte(ZbrojIgraca, 'I', G),
    ZbrojDealera > ZbrojIgraca,
    writeln('LOSE!'),
    postaviIshodGrupe(G, l), !,
    sljedecaGrupa.

    

% poziva se jedan od predikata, s obzirom na to koja se opcija odabere (hit, stand, double, split)
izvrsiPotezIgraca(s) :-
    !, sljedecaGrupa.
    
% ako igraè nema jednake karte ili ako je igraè splitao veæ tri puta (ima ukupno èetiri grupe), tada igraè ne može više splitati.
izvrsiPotezIgraca(p) :-
    not(mozesplitati),
    writeln('Nije moguce split-ati!'),
    poteziIgraca('I').

% ako je igraè splitao manje od tri puta (ima ukupno manje od èetiri grupe), tada je split valjan
izvrsiPotezIgraca(p) :-
    retract(ukupnoGrupa(U)), !, U1 is U + 1,
    assert(ukupnoGrupa(U1)),
    splitaj,
    ulog(Ulog), uzmiNovac(Ulog), !,  % uzmimamo od igraèa još novca, buduæi da je koristio split
    poteziIgraca('I').
    
izvrsiPotezIgraca(h) :-
    trenutnaGrupa(G),
    ukupnoGrupa(U),
    uzmiKartu(Karta), zbrojiKarte(Z, 'I', G),
    write('Nova karta: '), write(Karta), ( U > 1 -> (write(', Grupa: '), write(G)); true ), nl, !,
    ( Z > 21 -> ( writeln('BUST!'), postaviIshodGrupe(G, l), sljedecaGrupa ); poteziIgraca('I') ).
    

izvrsiPotezIgraca(d) :-
    trenutnaGrupa(G),
    brojKartiURukama('I', N, G), N > 2,
    writeln('Nije moguce duplirati! U ruci imate vise od 2 karte.'),
    poteziIgraca('I').
    

% ako igraè ima 2 karte u rukama, tada može duplirati
izvrsiPotezIgraca(d) :-
    uzmiKartu(Karta), trenutnaGrupa(G),
    ukupnoGrupa(Uk),
    write('Nova karta: '), write(Karta), ( Uk > 1 -> (write(', Grupa: '), write(G)); true ), nl,
    ulog(U), uzmiNovac(U),  % uzmimamo od igraèa još novca, buduæi da je koristio double
    dupliraj(G),
    zbrojiKarte(Z, 'I', G), !,
    ( Z > 21 -> ( writeln('BUST!'), postaviIshodGrupe(G, l), sljedecaGrupa ); sljedecaGrupa ).



% ako je na potezu dealer, a igraè je prethodno imao blackjack (bez splitova), tada dealer preskaèe igru
poteziIgraca('D') :-
    zbrojiKarte(21, 'I', 1), brojKartiURukama('I', 2, 1),
    ukupnoGrupa(1).

% ako je na potezu dealer, a igraè je prethodno imao zbroj manji jednak 21
poteziIgraca('D') :-
    trenutnaGrupa(Grupa),
    zbrojiKarte(ZbrojIgraca, 'I', Grupa), ZbrojIgraca =< 21,
    zbrojiKarte(ZbrojDealera, 'D', 1),
    (ZbrojDealera < 17 -> writeln('Nove karte dealera: '); true), izvrsiPotezDealera.
    
% ako je na potezu dealer, a igraèu su prethodno SVI grupe prešli 21, tada dealer preskaèe igru
poteziIgraca('D') :-
    svigrupePreko21.

% ako je na potezu dealer (i igraè je prethodno imao zbroj veæi od 21), dealer tada prelazi na sljedeæu grupu igraèa.
poteziIgraca('D') :-
    trenutnaGrupa(Grupa),
    zbrojiKarte(ZbrojIgraca, 'I', Grupa), ZbrojIgraca > 21, !,
    sljedecaGrupa.


    
% Ako na je na potezu igraè koji nije dealer: igraè unosi (h)it / (s)tand / (d)ouble / s(p)lit, sve dok mu je zbroj karti manji jednak 21 ili dok ne odustane sa (s)tand
% Ako je igraè dobio blackjack odmah sa prve dvije karte, casino ga isplaæuje u omjeru 3:2 (dobiveno / uloženo). Meðutim, ako i dealer ima blackjack, onda je push! Ovdje nije potrebno postaviti ishod grupe jer tu igra ionako prestaje i prelazi se na sljedeæe dijeljenje
poteziIgraca('I') :-
    brojKartiURukama('I', 2, 1),
    zbrojiKarte(21, 'I', 1),
    ukupnoGrupa(1),
    zbrojiKarte(Dealerove, 'D', 1),
    (Dealerove =:= 21 -> isplatiIgracaZaBlackjackPush; isplatiIgracaZaBlackjackWin ).
    
% Ako samo dealer ima blackjack, tada je igraè izgubio
poteziIgraca('I') :-
    brojKartiURukama('I', 2, 1),
    zbrojiKarte(Z, 'I', 1), Z =\= 21,
    ukupnoGrupa(1),
    zbrojiKarte(21, 'D', 1),
    prvaKartaDealera('A'),
    writeln('Dealer ima blackjack!').
    
% Ako igraè u rukama ima samo jednu kartu, daj mu još jednu
poteziIgraca('I') :-
    trenutnaGrupa(G),
    brojKartiURukama('I', 1, G),
    izvrsiPotezIgraca(h).
    
% Ako igraè može splitati (i ima novca za splitanje), dodajemo mu tu opciju
poteziIgraca('I') :-
    mozesplitati,
    ulog(U), novac(N), U =< N,
    writeln('Unesite opciju: (h)it / (s)tand / (d)ouble / s(p)lit:'), read(X),
    izvrsiPotezIgraca(X).

% Ako u rukama ima samo dvije karte, može koristiti i double
poteziIgraca('I') :-
    trenutnaGrupa(G),
    brojKartiURukama('I', 2, G),
    ulog(U), novac(N), U =< N,
    writeln('Unesite opciju: (h)it / (s)tand / (d)ouble:'), read(X),
    izvrsiPotezIgraca(X).
    
% Uvijek može koristiti hit/stand
poteziIgraca('I') :-
    writeln('Unesite opciju: (h)it / (s)tand:'), read(X),
    izvrsiPotezIgraca(X).


% prije poèetka svakog novog dijeljenja, provjerava se ukupni broj preostalih karata. Ako je taj broj manji od treæine špila, karte se miješaju. Takoðer se uklanjaju sve karte iz ruku igraèa i dealera
igraj :-
    pripremiIgru,
    ukupanBrojKarti(Broj), (Broj =< 104 -> promijesajKarte; true),
    unesiUlog,
    podijeliKarte(Skrivena),
    poteziIgraca('I'),
    promijeniIgracaNaPotezu,
    postaviNaPrvuGrupu,
    write('Skrivena karta dealera: '), write(Skrivena), nl,
    poteziIgraca('D'),
    promijeniIgracaNaPotezu,
    isplatiIgracuNovac(Dobiveno), ukupniUlog(Ulozeno),
    ( not(blackjack) -> ( Dobiveno >= Ulozeno -> writeln('Ukupno: WIN'); writeln('Ukupno: LOSE') ); true ),
    novac(Novac), write('Novac: '), write(Novac), nl, nl,
    writeln('Nova igra'),
    !, igraj.
