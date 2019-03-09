module Even.NatProofs

%access public export

evenNatSuccPlus : S (S (n + n)) = (S n + S n)
evenNatSuccPlus {n} = cong $ plusSuccRightSucc n n

