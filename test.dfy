class DequeCircular {
  var arr: array<int> // O array que armazena os elementos do deque
  var front: int // O índice do primeiro elemento do deque
  var rear: int // O índice do último elemento do deque
  var size: int // O número de elementos no deque

   var Elements: seq<int> // Representação abstrata dos elementos no deque
  const Capacity: int // A capacidade máxima do deque

  // Predicado para verificar a validade do deque

  predicate Valid() reads this {
      0 < arr.Length && // Ensure elements.Length is greater than 0
      0 <= front < arr.Length &&
      0 <= rear < arr.Length &&
      0 <= size <= arr.Length &&
      size == |Elements|
    }

  // Função fantasma para verificar se o deque está cheio
  function IsFull(): bool
    reads this
  {
    size == arr.Length
  }

  // Função fantasma para verificar se o deque está vazio
  function IsEmpty(): bool
    reads this
  {
    size == 0
  }

  // Construtor para inicializar um deque circular vazio com capacidade máxima
  constructor (capacity: int)
    requires capacity > 0
    ensures size == 0
    ensures Elements == []
    ensures Capacity == capacity
    ensures Valid()
  {
    arr := new int[capacity];
    front := 0;
    rear := capacity - 1;
    size := 0;
    Elements := [];
    Capacity := capacity;
  }

  // Adicionar um novo elemento ao final do deque
  method AddLast(e: int)
    requires !IsFull()
    requires arr.Length > 0
    ensures size == old(size) + 1
    ensures Elements == old(Elements) + [e]
    ensures Valid()
    modifies this, arr
  {
    rear := (rear + 1) % arr.Length;
    arr[rear] := e;
    size := size + 1;
    Elements := Elements + [e];
  }

  // Adicionar um novo elemento ao início do deque
  method AddFirst(e: int)
    requires !IsFull()
    ensures size == old(size) + 1
    ensures Elements == [e] + old(Elements)
    ensures Valid()
  {
    front := (front - 1 + arr.Length) % arr.Length;
    arr[front] := e;
    size := size + 1;
    Elements := [e] + Elements;
  }

  // Remover um elemento do final do deque e retornar seu valor
  method RemoveLast() returns (e: int)
    requires !IsEmpty()
    ensures size == old(size) - 1
    ensures Elements == old(Elements)[..|old(Elements)|-1]
    ensures e == old(Elements)[|old(Elements)|-1]
    ensures Valid()
  {
    e := arr[rear];
    rear := (rear - 1 + arr.Length) % arr.Length;
    size := size - 1;
    Elements := Elements[..|Elements|-1];
  }

  // Remover um elemento do início do deque e retornar seu valor
  method RemoveFirst() returns (e: int)
    requires !IsEmpty()
    ensures size == old(size) - 1
    ensures Elements == old(Elements)[1..]
    ensures e == old(Elements)[0]
    ensures Valid()
  {
    e := arr[front];
    front := (front + 1) % arr.Length;
    size := size - 1;
    Elements := Elements[1..];
  }

  // Verificar se um determinado elemento pertence ao deque
  method Contains(e: int) returns (contains: bool)
    ensures contains == (e in Elements)
    ensures Valid()
  {
    contains := e in Elements;
  }

  // Retornar o número de elementos do deque
  method Size() returns (s: int)
    ensures s == size
    ensures Valid()
  {
    s := size;
  }

  // Retornar a capacidade máxima do deque
  method GetCapacity() returns (c: int)
    ensures c == arr.Length
    ensures Valid()
  {
    c := arr.Length;
  }

  // Redimensionar o deque para um tamanho maior
  method Resize(newCapacity: int)
    requires newCapacity > arr.Length
    ensures Capacity == newCapacity
    ensures Elements == old(Elements)
    ensures Valid()
  {
    var newArr := new int[newCapacity];
    if front <= rear {
      var j := 0;
      var i := front;
      while i <= rear
        invariant 0 <= j < newArr.Length
        invariant front <= i <= rear + 1
        invariant j == i - front
      {
        newArr[j] := arr[i];
        i := i + 1;
        j := j + 1;
      }
    } else {
      var j := 0;
      var i := front;
      while i < arr.Length
        invariant 0 <= j < newArr.Length
        invariant front <= i <= arr.Length
        invariant j == i - front
      {
        newArr[j] := arr[i];
        i := i + 1;
        j := j + 1;
      }
      i := 0;
      while i <= rear
        invariant 0 <= j < newArr.Length
        invariant 0 <= i <= rear + 1
        invariant j == (arr.Length - front) + i
      {
        newArr[j] := arr[i];
        i := i + 1;
        j := j + 1;
      }
    }
    arr := newArr;
    front := 0;
    rear := size - 1;
  }
}

// Método Main para demonstrar o uso das operações implementadas
method Main()
{
  var deque := new DequeCircular(5);
  var size := deque.Size();
  var capacity := deque.GetCapacity();

  assert deque.IsEmpty();
  assert !deque.IsFull();
  assert size == 0;
  assert capacity == 5;

  deque.AddLast(1);
  deque.AddLast(2);
  deque.AddFirst(3);
  deque.AddFirst(4);
  deque.AddLast(5);

  size := deque.Size();
  assert size == 5;
  assert deque.IsFull();
  assert !deque.IsEmpty();

  var e := deque.RemoveFirst();
  assert e == 4;

  e := deque.RemoveLast();
  assert e == 5;

  size := deque.Size();
  assert size == 3;
  assert !deque.IsFull();
  assert !deque.IsEmpty();
  
  deque.Resize(10);
  capacity := deque.GetCapacity();
  size := deque.Size();
  assert capacity == 10;
  assert size == 3;

  deque.AddLast(6);
  deque.AddFirst(7);
  size := deque.Size();
  var contains7 := deque.Contains(7);
  var contains1 := deque.Contains(1);
  var contains5 := deque.Contains(5);
  
  assert size == 5;
  assert contains7;
  assert contains1;
  assert !contains5;
}
