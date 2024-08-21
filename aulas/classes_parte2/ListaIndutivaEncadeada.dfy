class ListaIndutivaEncadeada {
  var cabeca: int
  var cauda: ListaIndutivaEncadeada?
  var tamanho: nat

  ghost var Conteudo: seq<int>
  ghost var Repr: set<ListaIndutivaEncadeada>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    0 <= tamanho && tamanho ==  |Conteudo| &&
    (tamanho == 0 ==> Conteudo == [] && cauda == null) &&
    (tamanho != 0 ==>
       cauda != null && cauda in Repr &&
       cauda.Repr <= Repr && this !in cauda.Repr &&
       cauda.Valid() &&
       Conteudo == [cabeca] + cauda.Conteudo &&
       tamanho == cauda.tamanho + 1
    )
  }

  constructor() {}

  constructor Inicializar()
    ensures Valid()
    ensures Conteudo == []
  {
    cauda := null;
    tamanho := 0;
    Conteudo := [];
    Repr := {this};
  }

  method Cons(e:int) returns (r:ListaIndutivaEncadeada)
    requires Valid()
    ensures r.Valid()
    ensures r.Conteudo == [e] + Conteudo
  {
    r := new ListaIndutivaEncadeada();
    r.cabeca := e;
    r.cauda := this;
    r.tamanho := tamanho + 1;
    r.Conteudo := [e] + Conteudo;
    r.Repr := {r} + Repr;
  }

  method Concatenar(l:ListaIndutivaEncadeada) returns (r:ListaIndutivaEncadeada)
    requires Valid()
    requires l.Valid()
    ensures r.Valid()
    ensures r.Conteudo == Conteudo + l.Conteudo
    decreases Repr
  {
    if tamanho == 0
    {
      r := l;
    }
    else
    {
      var c := cauda.Concatenar(l);
      r := c.Cons(cabeca);
    }
  }

  function Tamanho():nat
    reads this
  {
    tamanho
  }
}

method Main()
{
  var lista1 := new ListaIndutivaEncadeada.Inicializar();
  assert lista1.Conteudo == [];
  var lista2 := lista1.Cons(1);
  assert lista2.Conteudo == [1];
  var lista3 := lista2.Cons(2);
  assert lista3.Conteudo == [2,1];
  assert lista1.Tamanho() == 0;  
  assert lista2.Tamanho() == 1;
  assert lista3.Tamanho() == 2;
}