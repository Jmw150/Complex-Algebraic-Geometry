open Base

let listcheck () = 
  assert (List.equal Int.equal (List.rev [3;2;1]) [1;2;3])
    
