/*
Integrantes:
  - Israel Garcia
  - Marcos Sanhudo
  - Arthur Mariano
  - Arthur Viegas
  - Felipe Fagundes
*/

class {:autocontracts} Deque 
{
  // campos
  var   elements : array<int>
  var   head     : nat 
  var   tail     : nat 
  var   size     : nat
  const max      : nat

  ghost var   Repr     : set<object>
  ghost var   Conteudo : seq<int>
  ghost const Max      : nat

  ghost predicate Valid() 
    reads this, Repr
    ensures Valid() ==> this in Repr
    { 
      && this in Repr
      && elements in Repr
      && max >= 0
      && elements.Length == max
      && 0 < max 
      && 0 <= head < max
      && 0 <= tail < max
      && 0 <= size <= max
      && Max == max                               
      && size == |Conteudo|
      && ((head < tail ==> Conteudo == elements[head..tail])
      && (head > tail ==> Conteudo == elements[head..] + elements[..tail])
      && (head == tail ==> ((head == 0 && size == 0) ==> Conteudo == []) && (head == 0 && size == 1 ==>  Conteudo == [elements[head]])))
    }
    
  constructor (l:nat)
    requires l > 0
    ensures Valid() && fresh(Repr)
    ensures Max == l
    ensures Conteudo == []
    ensures head == 0
    ensures tail == 0
    ensures size == 0
    {
      max      := l;
      elements := new int[l];
      size     := 0;
      head     := 0;
      tail     := 0;
      Conteudo := [];
      Max      := max;
      Repr     := {this, elements};
    }

  method AddOnTail(e:int)
    requires Valid()
    requires |Conteudo| < Max
    requires size < Max
    modifies Repr
    ensures Valid()
    ensures Conteudo == old(Conteudo) + [e]
    ensures |Conteudo| == old(|Conteudo|) + 1
    ensures size <= Max
    
    {
      elements[tail] := e;
      tail           := (tail+1) % max;
      size           := size + 1;
      Conteudo       := Conteudo + [e];
      
      assert size <= max;
      assert size == old(size) + 1;
    }

method AddOnHead(e:int) 
  requires Valid()
  requires |Conteudo| < Max
  requires size < Max
  modifies Repr
  ensures Valid()
  ensures Conteudo == [e] + old(Conteudo)
  ensures size <= Max
{
  Conteudo := [e] + Conteudo;
  size := size + 1;
  assert size == old(size) + 1;
  assert size <= Max;
}

method PopFromTail() returns (i: int)
  requires Valid()
  requires size > 0
  modifies Repr
  ensures Valid()
  ensures i == elements[tail]
  ensures size == old(size) - 1
{
  i := elements[tail];

  if (head <= tail) {
    Conteudo := elements[head..tail];
  } else if (tail < head) {
    Conteudo := elements[..tail] + elements[head..];
  } else {
    Conteudo := elements[..tail] + elements[head + 1..];
  }
  
  size := size - 1;
}

method PopFromHead() returns (i: int)
  requires Valid()
  requires size > 0
  modifies Repr
  ensures Valid()
  ensures i == elements[head]
  ensures size == old(size) - 1
{
  i := elements[head];

  if (head <= tail) {
    Conteudo := elements[head..tail];
  } else if (tail < head) {
    Conteudo := elements[..tail + 1] + elements[head + 1..];
  } else {
    Conteudo := elements[..tail] + elements[head + 1..];
  }
  
  size := size - 1;
}

method Contains(e: int) returns (b: bool)
    requires Valid()
    ensures Valid()
    ensures elements == old(elements)
    ensures Repr == old(Repr)
    ensures size == old(size)
    ensures [e] <= Conteudo
  {
    var index: nat := head;
    var count: nat := 0;
    b := false;
    while count < size 
      invariant InRange(index)
      invariant count <= size
    {
      if (elements[index] == e) {
        b := true;
        break;
      }
      assert InRange(index);
      index := ((index + 1) % max);
      assert InRange(index);
      count := count + 1;
    }
  }

  predicate InRange(n:nat)
    requires Valid()
    ensures Valid()
    ensures (head < tail)  ==> InRange(n) == (head < n && n < tail)
    ensures (head > tail)  ==> InRange(n) == (n < max && n < head)
    ensures (head == tail) ==> InRange(n) == (n == head && n == tail)
    ensures n >= 0 && n < Max
  {   
    if (head < tail) then
        head <= n && n <= tail
    else if (head > tail) then
        n < max && n <= head
    else
        n == head && n == tail
  }
  
  function MaxSize():nat
    requires Valid() 
    reads Repr
    ensures MaxSize() == Max
  {
    max
  }

  function Size():nat
    requires Valid()
    reads Repr
    ensures Size() == |Conteudo|
  {
    size
  }

  function Full():bool
    requires Valid()
    reads Repr
    ensures Full() == (|Conteudo| == Max)
  {
    size == max
  }

  function Empty():bool
    requires Valid()
    reads Repr
    ensures Empty() == (|Conteudo| == 0)
  {
    size == 0
  }
}

method Main()
{
  var q := new Deque(8);
  assert q.Empty();
  assert q.MaxSize() == 8;
  q.AddOnTail(1);
  assert !q.Empty();
  assert q.Size() == 1;
  q.AddOnHead(123);
  assert q.Size() == 2;
  assert !q.Full();
  var ret_popFromTail := q.PopFromTail();
  assert q.Size() == 1;
  var ret_popFromHead := q.PopFromHead();
  assert q.Size() == 0;
  q.AddOnHead(1);
  q.AddOnHead(3);
  q.AddOnHead(7);
  q.AddOnHead(13);
  q.AddOnHead(17);
  q.AddOnHead(19);
  q.AddOnHead(29);
  q.AddOnHead(31);
  assert q.Size() == 8;
  assert q.Full();
  assert q.MaxSize() == 8;
}
