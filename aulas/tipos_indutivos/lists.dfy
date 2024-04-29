// tipos indutivos -> tipos algebricos em linguagens de prog
// tipos imutaveis

// a palavra 'Vazia' é um simbolo que representa qualquer coisa
// Cons -> construtor
// representacao de Lista como um ENUM
datatype Lista<T> = Vazia | Cons(cabeca:T, cauda:Lista<T>)

function Tamanho<T>(list: Lista<T>):nat
{
    // if list == Vazia
    // then 0
    // else 1 + Tamanho(list.cauda)
    // ou, usar Casamento de ...
    match list
    case Vazia     => 0
    case Cons(h,l) => 1 + Tamanho(l)  
}

function Concatenar<T>(x:Lista<T>, y:Lista<T>):Lista<T>
ensures Tamanho(Concatenar(x,y)) == Tamanho(x) + Tamanho(y)
{
    match x
    case Vazia     => y
    case Cons(h,l) => Cons(h, Concatenar(l,y))  
}

// prova
lemma ConcatenarAssociatividade<T>(x:Lista<T>, y:Lista<T>, z:Lista<T>)
ensures Concatenar(x, Concatenar(y,z)) == Concatenar(Concatenar(x,y),z)
{}

method Main()
{
    var lista1:Lista<int> := Vazia;
    var lista2 := Cons(1, lista1);
    var lista3 := Cons(1, Cons(2,lista1));
    assert Tamanho(lista1) == 0;
    assert Tamanho(lista2) == 1;
    assert Tamanho(lista3) == 2;
    var lista4 := Concatenar(lista2, lista3);
    assert Tamanho(lista4) == 3;
}