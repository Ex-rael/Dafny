class Celula
{
  var dados: int
  constructor ()
    ensures dados == 0
  {
    dados := 0;
  }
}

class Contador
{
  //Contador é representado pelo número
  //de operações de incremento e decremento
  //armazenadas em um objeto Celula
  var incs: Celula
  var decs: Celula
  //valor é uma representação abstrata
  ghost var valor: int
  //Controle de frames dinâmicos
  //Repr é a coleção de objetos que representam a classe sendo implementada
  //Nesse caso serão this, incs e decs
  ghost var Repr: set<object>

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    incs in Repr &&
    decs in Repr &&
    incs != decs && //necessário para evitar referência ao mesmo objeto Celula
    incs.dados >= 0 &&
    decs.dados >= 0 &&
    valor == incs.dados - decs.dados
  }

  constructor ()
    ensures Valid()
    ensures fresh(Repr) //necessário para indicar que não reusa memória "externa" ao objeto
    ensures valor == 0
  {
    incs := new Celula();
    decs := new Celula();
    valor := 0;
    Repr := {this, incs, decs};
  }

  method Incrementa()
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr)) //necessário para indicar qual alteração de Repr é válida
    ensures valor == old(valor) + 1
  {
    incs.dados := incs.dados + 1;
    valor := valor + 1;
  }

  method Decrementa()
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures fresh(Repr - old(Repr))
    ensures valor == old(valor) - 1
  {
    decs.dados := decs.dados + 1;
    valor := valor - 1;
  }

  function GetValor():int
    requires Valid()
    reads Repr
    ensures Valid()
    ensures GetValor() == valor
  {
    incs.dados - decs.dados
  }
}

method Main()
{
  var c := new Contador();
  c.Incrementa();
  c.Incrementa();
  c.Decrementa();
  c.Incrementa();
  var v := c.GetValor();
  assert v == 2;
}