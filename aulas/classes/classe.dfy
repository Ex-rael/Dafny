class Celula
{ // objeto de dados simples
    var dado:int
    constructor ()
    ensures dado == 0
    {
        dado := 0;
    }
}

class Contador
{
    // especificação abstrata
    ghost var valor:int

    // controle dos frames dinamicos
    ghost var Repr:set<object> // representation -> substitui a manipulação individual dos frames de leitura de cada objeto
    // implementação concreta
    var incs: Celula
    var decs: Celula


    //invariante da classe
    ghost predicate Valid()
    reads this, incs, Repr // só garante leitura do Contador, e seus atributos, mas não os atributos dos atributos
    ensures Valid() ==> this in Repr // 
    {
        // atribui ao Repr todos os objetos que serão 'gerenciados' por ele
        && this in Repr
        && incs in Repr
        && decs in Repr

        && incs != decs  // se não informar que os dois objetos devem ser diferentes, não pode ser provado de que dois objetos do mesmo tipo não são O MESMO OBJETO
        && incs.dado >= 0 
        && decs.dado >= 0 
        && valor == incs.dado - decs.dado       
    }

    constructor()
    ensures Valid()
    ensures valor == 0
    ensures fresh(Repr) // garante que tudo que está contido em Repr está sendo criado nesse momento
    {
        incs := new Celula();
        decs := new Celula();
        valor := 0;
        Repr := {this, incs, decs};
    }

    method Incrementar()
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures valor == old(valor) + 1
    ensures fresh(Repr - old(Repr)) // unica coisa nova criada após a execucao de Incrementar é a diferenca entre os conjuntos | em resumo, continua o mesmo. os conjuntos não são alterados
    {
        incs.dado := incs.dado + 1;
        valor := valor + 1;
    }

    method Decrementar()
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures valor == old(valor) - 1
    {
        decs.dado := decs.dado + 1;
        valor := valor - 1;
    }

    function GetValor():int
    requires Valid()
    reads Repr
    ensures Valid()
    ensures GetValor() == valor
    {
      incs.dado - decs.dado  
    }
}

method Main()
{
    var c1 := new Contador();
    assert c1.GetValor() == 0;
    c1.Incrementar();
    assert c1.GetValor() == 1;
    c1.Decrementar();
    assert c1.GetValor() == 0;
    }