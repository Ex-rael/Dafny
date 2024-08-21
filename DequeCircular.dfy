module DequeCircularModule {
  class DequeCircular {
    var elements: array<int>;
    var head: int;
    var tail: int;
    var size: int;

    var abstract_elements: seq<int>;

    predicate Valid() reads this {
      0 < elements.Length && // Ensure elements.Length is greater than 0
      0 <= head < elements.Length &&
      0 <= tail < elements.Length &&
      0 <= size <= elements.Length &&
      size == |abstract_elements|
    }

    predicate IsFull() reads this {
      size == elements.Length
    }

    predicate IsEmpty() reads this {
      size == 0
    }

    constructor(capacity: int)
      requires capacity > 0
      ensures Valid()
    {
      elements := new int[capacity];
      head := 0;
      tail := 0;
      size := 0;
      abstract_elements := [];
    }

    method AddToRear(value: int)
      requires !IsFull()
      modifies this
      ensures Valid()
    {
      assert Valid();
      assert 0 <= tail < elements.Length;
      elements[tail] := value;
      tail := (tail + 1) % elements.Length;
      size := size + 1;
      abstract_elements := abstract_elements + [value];
      assert Valid();
    }

    method AddToFront(value: int)
      requires !IsFull()
      modifies this
      ensures Valid()
    {
      assert Valid();
      head := (head - 1 + elements.Length) % elements.Length;
      assert 0 <= head < elements.Length;
      elements[head] := value;
      size := size + 1;
      abstract_elements := [value] + abstract_elements;
      assert Valid();
    }

    method RemoveFromRear() returns (value: int)
      requires !IsEmpty()
      modifies this
      ensures Valid()
    {
      assert Valid();
      tail := (tail - 1 + elements.Length) % elements.Length;
      assert 0 <= tail < elements.Length;
      value := elements[tail];
      size := size - 1;
      abstract_elements := abstract_elements[..|abstract_elements|-1];
    }

    method RemoveFromFront() returns (value: int)
      requires !IsEmpty()
      modifies this
      ensures Valid()
    {
      assert 0 <= head < elements.Length;
      value := elements[head];
      head := (head + 1) % elements.Length;
      size := size - 1;
      abstract_elements := abstract_elements[1..];
      assert Valid();
    }

    method Contains(value: int) returns (found: bool)
      ensures Valid()
    {
      found := false;
      var i := 0;
      while (i < size)
        invariant 0 <= i <= size
        invariant Valid()
      {
        if (elements[(head + i) % elements.Length] == value) {
          found := true;
          break;
        }
        i := i + 1;
      }
    }

    method Size() returns (n: int)
      ensures n == size
      ensures Valid()
    {
      n := size;
    }

    method Capacity() returns (n: int)
      ensures n == elements.Length
      ensures Valid()
    {
      n := elements.Length;
    }

    method Empty() returns (b: bool)
      ensures b == IsEmpty()
      ensures Valid()
    {
      b := IsEmpty();
    }

    method Full() returns (b: bool)
      ensures b == IsFull()
      ensures Valid()
    {
      b := IsFull();
    }

    method Resize(newCapacity: int)
      requires newCapacity > size
      modifies this
      ensures Valid()
    {
      var newElements := new int[newCapacity];
      var i := 0;
      while (i < size)
        invariant 0 <= i <= size
        invariant Valid()
      {
        newElements[i] := elements[(head + i) % elements.Length];
        i := i + 1;
      }
      elements := newElements;
      head := 0;
      tail := size;
      abstract_elements := abstract_elements;  // This line is actually redundant
      // No change in abstract_elements, since elements are copied
      assert Valid();
    }
  }

  method Main() {
    var deque := new DequeCircular(3);
    assert deque.Valid();

    deque.AddToRear(1);
    deque.AddToRear(2);

    var full := deque.IsFull();
    assert !full;

    deque.AddToFront(0);
    full := deque.IsFull();
    assert full;

    var size := deque.Size();
    assert size == 3;

    var frontValue := deque.RemoveFromFront();
    assert frontValue == 0;

    size := deque.Size();
    assert size == 2;

    var rearValue := deque.RemoveFromRear();
    assert rearValue == 2;

    size := deque.Size();
    assert size == 1;

    deque.Resize(5);
    var capacity := deque.Capacity();
    assert capacity == 5;

    size := deque.Size();
    assert size == 1;
  }
}
