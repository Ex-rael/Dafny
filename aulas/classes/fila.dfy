class Fila // rascunho T2
{
    // abstração 
    ghost var Conteudo:seq<nat> // coleção linear, sequencia
    ghost const TamanhoMaximo:nat
    ghost var Repr:set<object>

    // implementacao 
    var a:array<nat>
    const max:nat

    // incariante de classe 
    ghost predicate Valid()
    ensures Valid() ==> this in Repr

    constructor (m:nat)
    requires m > 0 // é o tamanho
    ensures Valid()
    ensures fresh(Repr)
    ensures TamanhoMaximo == m
    ensures Conteudo == []
    {
        // ...
    }

    method Enfileirar(e:nat)
    requires Valid()
    requires |Conteudo| < TamanhoMaximo
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr)) // a unica coisa NOVA que pode surgir deverá ter sido criado durante o método
    ensures Conteudo == old(Conteudo) + [e] // concatena ao final

    // method Desenfileirar
}