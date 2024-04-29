method Mult(x:int, y:int) returns (r:int)
  requires x >= 0 && y >= 0
  ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    while m > 0
      invariant x * y == (m * n) + r
    {
        r := r + n;
        m := m - 1;
    }
}