method Add(x: int, y: int) returns (r: int)
  requires 0 <= x && 0 <= y
  ensures r == 2*x + y
{
  r := 2*x;
  var n:int := y;
  while n > 0
    invariant r == 2*x+y-n && 0 <= n
  {
    r := r + 1;
    n := n - 1;
  }
}


