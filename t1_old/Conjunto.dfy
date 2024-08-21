class {:autocontracts} ConjuntoInteiros{

  var conjunto: array<int>

  ghost var conjuntoSet: set<int>
  ghost predicate Valid() {
    (forall i:: 0<=i< conjunto.Length ==> conjunto[i] in conjuntoSet)
    &&(conjunto.Length == |conjuntoSet|)

  }

  //Construtor deve instanciar um conjunto vazio
  constructor()
    ensures conjuntoSet == {}
    ensures |conjuntoSet| == 0

  method Adicionar(n: int) returns(res: bool)
    modifies Repr, conjunto
    ensures res != (n in old(conjuntoSet))
    ensures n !in old(conjuntoSet) ==>|conjuntoSet| == old(|conjuntoSet|+1)
    ensures n in old(conjuntoSet) ==>|conjuntoSet| == old(|conjuntoSet|)
    ensures n !in old(conjuntoSet) ==> conjuntoSet - {n} == old(conjuntoSet)
    ensures n in old(conjuntoSet) ==> conjuntoSet == old(conjuntoSet)
    ensures n in conjuntoSet
    ensures forall i:: 0<=i< conjunto.Length ==> conjunto[i] in conjuntoSet
    ensures conjunto.Length == |conjuntoSet|

  method Remover(n: int) returns(res: bool)
    modifies Repr, conjunto
    ensures res == (n in old(conjuntoSet))
    //Retorna true para => tamanho igual caso haja remoção
    ensures n in old(conjuntoSet) ==>|conjuntoSet| == old(|conjuntoSet|-1)
    //Retorna true para => tamanho igual caso não haja remoção
    ensures n !in old(conjuntoSet) ==>|conjuntoSet| == old(|conjuntoSet|)
    //Verifica se o conjunto atual + o n é igual ao conjunto antigo, se true então n foi removido
    ensures n in old(conjuntoSet) ==> conjuntoSet + {n} == old(conjuntoSet)
    //Verifica se o conjunto atual é igual(elementos) ao conjunto antigo, não não contem no conjunto
    ensures n !in old(conjuntoSet) ==> conjuntoSet == old(conjuntoSet)
    // n não pertecnte a lista de conjuntos
    ensures n !in conjuntoSet
    //verifica se todos para todos o conjunto, se o elemento do conjunto do array pertence ao conjunto set
    ensures forall i:: 0<=i< conjunto.Length ==> conjunto[i] in conjuntoSet
    //verifica se o tamanho do array é igual ao tamanho do set
    ensures conjunto.Length == |conjuntoSet|


  method Pertence(n: int) returns(res: bool)
    ensures conjuntoSet == old(conjuntoSet)
    ensures res == (n in conjuntoSet)


  method Tamanho() returns(res: int)
    ensures conjuntoSet == old(conjuntoSet)
    ensures res == |conjuntoSet|


  method Vazio() returns(res: bool)
    ensures conjuntoSet == old(conjuntoSet)
    ensures res == (|conjuntoSet| == 0)
  {
    res :=  conjunto.Length == 0;
  }

  method AdicionarArray(a: array<int>) returns(res: bool)
    modifies Repr, conjunto
    ensures forall i:: 0<=i< a.Length  ==> a[i] !in conjuntoSet
    ensures |old(conjuntoSet)| + a.Length == |conjuntoSet|

  {
    
    res := forall i:: 0<=i< a.Length  ==> a[i] in conjunto;
  }

  static method Main() {
    var conjunto := new ConjuntoInteiros();
    var b : array<int>;

    var x := conjunto.Vazio();
    assert x;
    assert conjunto.conjuntoSet == {};

    x := conjunto.Adicionar(5);
    assert x;
    assert conjunto.conjuntoSet == {5};

    x := conjunto.Adicionar(5);
    assert x == false;

    x := conjunto.AdicionarArray(b);
    assert x == true;

  }

}
