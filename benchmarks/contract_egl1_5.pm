// Randomized Protocol for Signing Contracts [Even, Goldreich and Lempel 1985]
// Gethin Norman and Vitaly Shmatikov 2004

dtmc

// CONSTANTS
const int N=10; // number of pairs of secrets
const int L=2; // number of bits in each secret

// FORMULE
// B knows a pair of secrets
formula kB = ( (a0=L & a5=L)
			 | (a1=L & a6=L)
			 | (a2=L & a7=L)
			 | (a3=L & a8=L)
			 | (a4=L & a9=L));
// A knows a pair of secrets
formula kA = ( (b0=L & b5=L)
			 | (b1=L & b6=L)
			 | (b2=L & b7=L)
			 | (b3=L & b8=L)
			 | (b4=L & b9=L));

module protocol
	
	b : [1..L]; // counter for current bit to be send
	n : [0..N-1]; // counter for which secret to send
	phase : [1..4]; // phase of the protocol
	// 1 - sending secrets using OT (step 1 of the protocol)
	// 2 - send bits of the secrets 0,...,N-1 (step 2 of the protocol)
	// 3 - send bits of the secrets N,...,2N-1 (step 2 of the protocol)
	party : [1..2]; // which party sends next (1 - A and 2 - B)
	
	// STEP 1 
	// A sends
	[receiveB] phase=1 & party=1 -> (party'=2);
	 // B sends and we move onto the next secret
	[receiveA] phase=1 & party=2 & n<N-1 -> (party'=1) & (n'=n+1);
	// B sends and finished this step
	[receiveA] phase=1 & party=2 & n=N-1 -> (party'=1) & (phase'=2) & (n'=0);
	// STEP 2 (A sends)
	// next secret
	[receiveB] (phase=2 | phase=3) & party=1 & n<N-1-> (n'=n+1);
	// move onto secrets N,...,2N-1	
	[receiveB] phase=2 & party=1 & n=N-1 -> (phase'=3) & (n'=0);
	// move onto party B
	[receiveB] phase=3 & party=1 & n=N-1 -> (phase'=2) & (party'=2) & (n'=0);
	// STEP 2 (B sends)
	// next secret
	[receiveA] (phase=2 | phase=3) & party=2 & n<N-1 -> (n'=n+1);
	// move onto secrets N,...,2N-1	
	[receiveA] phase=2 & party=2 & n=N-1 -> (phase'=3) & (n'=0);
	 // move onto next bit
	[receiveA] phase=3 & party=2 & n=N-1 & b<L 
	-> (phase'=2) & (party'=1) & (n'=0) & (b'=b+1);
	// finished protocol
	[receiveA] phase=3 & party=2 & n=N-1 & b=L -> (phase'=4);
	// FINISHED
	[] phase=4 -> (phase'=4); // loop
	
endmodule

module partyA
	
	// bi the number of bits of B's ith secret A knows 
	// (keep pairs of secrets together to give a more structured model)
	b0 : [0..L]; b5 : [0..L];
	b1 : [0..L]; b6 : [0..L];
	b2 : [0..L]; b7 : [0..L];
	b3 : [0..L]; b8 : [0..L];
	b4 : [0..L]; b9 : [0..L];
	
	// first step (get either secret i or (N-1)+i with equal probability)
	[receiveA] phase=1 & n=0 -> 0.5 : (b0'=L) + 0.5 : (b5'=L);
	[receiveA] phase=1 & n=1 -> 0.5 : (b1'=L) + 0.5 : (b6'=L);
	[receiveA] phase=1 & n=2 -> 0.5 : (b2'=L) + 0.5 : (b7'=L);
	[receiveA] phase=1 & n=3 -> 0.5 : (b3'=L) + 0.5 : (b8'=L);
	[receiveA] phase=1 & n=4 -> 0.5 : (b4'=L) + 0.5 : (b9'=L);
	// second step (secrets 0,...,N-1)
	[receiveA] phase=2 & n=0 -> (b0'=min(b0+1,L));
	[receiveA] phase=2 & n=1 -> (b1'=min(b1+1,L));
	[receiveA] phase=2 & n=2 -> (b2'=min(b2+1,L));
	[receiveA] phase=2 & n=3 -> (b3'=min(b3+1,L));
	[receiveA] phase=2 & n=4 -> (b4'=min(b4+1,L));
	// second step (secrets N,...,2N-1)
	[receiveA] phase=3 & n=0 -> (b5'=min(b5+1,L));
	[receiveA] phase=3 & n=1 -> (b6'=min(b6+1,L));
	[receiveA] phase=3 & n=2 -> (b7'=min(b7+1,L));
	[receiveA] phase=3 & n=3 -> (b8'=min(b8+1,L));
	[receiveA] phase=3 & n=4 -> (b9'=min(b9+1,L));
	
endmodule

// construct module for party B through renaming
module partyB=partyA[b0=a0,b1=a1,
                     b2=a2,b3=a3,
                     b4=a4,b5=a5,
                     b6=a6,b7=a7,
                     b8=a8,b9=a9,
                     receiveA=receiveB]
endmodule
