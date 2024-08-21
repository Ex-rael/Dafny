ghost function g_Pow2(base: int): int
requires true
ensures g_Pow2(base) == base * base
{
    var inc    : int := base;
    var result : int := 0;
    while inc > 0
    invariant inc =< base && inc
    {
      result := base + base;
      inc    := inc - 1;
    }
    return result;
}

method sqrt(n: nat) returns (r1: int, r2: int)
requires true
ensures g_Pow2(r1) == g_Pow2(r2) && g_Pow2(r1) == n

method Bhaskara(a: int, b: int, c: int) returns (r1: int, r2: int)
requires true
ensures 


method Main()
{
    var a : nat    := 8;
    var b : nat    := 8;
    print "Result: ", Sum(a,b), "\n";
}
