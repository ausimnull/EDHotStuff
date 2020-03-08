----------------------------- MODULE EDHotStuff -----------------------------
 EXTENDS Integers, Sequences, FiniteSets, TLC
 (**************************************************************************)
 (*                                                                        *)
 (*                             VERSION 1.0                                *)
 (*                                                                        *)
 (* This module is a specification based on Algorithms 4, and 5, in the    *)
 (* HotStuff white paper.                                                  *)
 (*                                                                        *)
 (* AUTHOR = "Maofan Yin, Dahlia Malkhi, Michael K. Reiter,                *)
 (*           Guy Golan Gueta, Ittai Abraham",                             *)
 (* TITLE = "HotStuff: BFT Consensus in the Lens of Blockchain",           *)
 (* Journal = "arXiv: 1803.05069v6 [CS.DC])",                              *)
 (* YEAR = 2019,                                                           *)
 (*                                                                        *)
 (* In as much as is possible it uses the same notation as the published   *)
 (* algorithms.  There are several parts that are implementation           *)
 (* dependent, namely how the parent chains are implemented, and how       *)
 (* leaders are selected.  I have chosen the simplest possible             *)
 (* implemetations in this version.                                        *)
 (*                                                                        *)
 (* This version is incomplete, but does run in the TLC model checker.  No *)
 (* attempt has been made yet to define any invariants                     *)
 (*                                                                        *)
 (**************************************************************************) 

----------------------------------------------------------------------------
CONSTANT Value, Acceptor, FakeAcceptor

CONSTANTS
        ByzQuorum  \* not currently used
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
    
ViewNums == Nat 

None == CHOOSE v : v \notin Value /\ v \notin Acceptor /\ v \notin FakeAcceptor
   
(***************************************************************************)
(* The following operator definitions allow us to form a TYPE_OK           *)
(* invariant.                                                              *)
(* Note that Leaf needs to be a recursive definition -                     *)
(***************************************************************************)
    
RECURSIVE Leaf       
QCElement ==    [viewNum : ViewNums, node : Leaf,      sig : Acceptor]           
Leaf      ==    [parent  : Acceptor, cmd  : Value, justify : {}, height : {}]

Message   ==    [type: "generic", viewnum : ViewNums, node : Leaf, justify : << >>]
           \cup [type: "newview", viewnum : ViewNums, node : Leaf, justify : << >>] \* always sent to leader

\* QC = ???? FIXME
           
EmptyQC   ==    {}
EmptyNode ==    [parent : {}, cmd : {}, justify : {}, height : {}]
EmptyV    ==    [x \in {} |-> TRUE]  \* empty function (nothing is TRUE !)

ByzAcceptor == Acceptor \cup FakeAcceptor

genesis_null  ==  [ parent  |-> << 
                                 << >> 
                               >>, 
                   cmd     |-> "genesis_null",
                   justify |-> [ viewnum |-> 0, 
                                 node    |-> << >>,
                                 sig     |-> 1
                               ],
                   height  |-> 0

                 ]
                 
genesis_bpp  ==  [ parent  |-> << 
                                 << genesis_null >> 
                               >>, 
                   cmd     |-> "genesis_bpp",
                   justify |-> [ viewnum |-> 0, 
                                 node    |-> genesis_null,
                                 sig     |-> 1
                               ],
                   height  |-> 1

                 ]
                 
genesis_bp   ==  [ parent  |-> << 
                                 << genesis_bpp >> 
                               >>, 
                   cmd     |-> "genesis_bp",
                   justify |-> [ viewnum |-> 0, 
                                 node    |-> genesis_bpp,
                                 sig     |-> 1
                               ],
                   height  |-> 2

                 ]

genesis_b    ==  [ parent  |-> << 
                                 << genesis_bp >> 
                               >>, 
                   cmd     |-> "genesis_b",
                   justify |-> [ viewnum |-> 0, 
                                 node    |-> genesis_bp,
                                 sig     |-> 1
                               ],
                   height  |-> 3

                 ]
                                
\* genesis              
b0           ==  [ parent  |-> << 
                                 << genesis_b >> 
                               >>, 
                   cmd     |-> "b0",
                   justify |-> [ viewnum |-> 0, 
                                 node    |-> genesis_b,
                                 sig     |-> 1
                               ],
                   height  |-> 4

                 ]
 
 NextValue(sent) == CHOOSE x \in Value : x \notin sent
                    
 
(***************************************************************************)
(* TODO                                                                    *)
(*                                                                         *)
(* We can make OnCommit(node) recursive if we define it as an operator     *)
(*                                                                         *)
(* RECURSIVE OnCommit(_) OnCommit(self) == /\ IF bexec[self].height <      *)
(* node[self].height /* define node globally above                         *)
(*                         THEN /\ node[self] = node[self].parent[1][1]    *)
(*                              /\ OnCommit(self)                          *)
(*                           \* /\ EXCECUTE(node.cmd)                      *)
(*                              /\ UNCHANGED << b0, values, voteChannel,   *)
(*                                              newViewChannel,            *)
(*                                              proposalChannel,           *)
(*                                              lastReadProposal, vheight, *)
(*                                              block, bexec, qchigh,      *)
(*                                              bleaf, curView, V, b, bp,  *)
(*                                              bpp,                       *)
(*                                              emptyQueueFlag, qc, mvote, *)
(*                                              mprop, mnew, parent,       *)
(*                                              VEntry, bpropose, c, qch,  *)
(*                                              vb, tmp, key, val,         *)
(*                                              bstar >>                   *)
(*                                                                         *)
(***************************************************************************)
        
(****
--algorithm EDHotStuff {
    variables
        (*******************************************************************)
        (* We first construct the root node b0. Just how the parent        *)
        (* part of a Leaf is constructed is implementation dependent,      *)
        (* so for now we define it as follows -                            *)
        (*                                                                 *)
        (* A parent is an ordered list << [node], ... >> of ancestors.     *)
        (*                                                                 *)
        (* b0 is the same genesis node known by all correct replicas.      *)
        (*                                                                 *)
        (* The HS paper suggests using hashes of nodes to implement the    *)
        (* parent field, with a lookup table. For this specification,      *)
        (* we'll just use the actual node, as we can't easily use any      *)
        (* crypto in TLA+.                                                 *)
        (* We can place dummy parent records in the list to extend it      *)
        (* to the correct height.                                          *)
        (*                                                                 *)
        (*******************************************************************)
        Ledger              = [a \in Acceptor |-> << >>],       \* A ledger for each Acceptor  
        sentValues          = {},   
        
        \* communication channels
        voteChannel         = [a \in Acceptor |-> << >>],
        newViewChannel      = [a \in Acceptor |-> << >>],
        proposalChannel     = << >>,                            \* global, as this is for broadcasts
        lastReadProposal    = [a \in Acceptor |-> 0],
    
        \* per process state variables (as per HS paper)
        vheight             = [a \in Acceptor |-> 0],           \* height of last voted node.
        block               = [a \in Acceptor |-> EmptyNode],   \* locked node (similar to lockedQC ).
        bexec               = [a \in Acceptor |-> EmptyNode],   \* last executed node.
        qchigh              = [a \in Acceptor |-> << >>],       \* highest known QC (similar to genericQC ) kept by a Pacemaker.
        bleaf               = [a \in Acceptor |-> EmptyNode],   \* leaf node kept by PaceMaker
        curView             = [a \in Acceptor |-> 0],     
        V                   = [a \in Acceptor |-> EmptyV], 
        
        \* the 3-chain
        b                   = [a \in Acceptor |-> EmptyNode],
        bp                  = [a \in Acceptor |-> EmptyNode],
        bpp                 = [a \in Acceptor |-> EmptyNode],
        
        \* internal variables
        nextEventFlag       = [a \in Acceptor |-> FALSE],
        nextEventLOCK       = [a \in Acceptor |-> FALSE],
        qc                  = [a \in Acceptor |-> << >>],
        mvote               = [a \in Acceptor |-> << >>],
        mprop               = [a \in Acceptor |-> << >>],
        mnew                = [a \in Acceptor |-> << >>], 
        VEntry              = [a \in Acceptor |-> {}],        
             
    define {
        CreateLeaf(p, v2, qc1, h) == [parent |-> p, cmd |-> v2, justify |-> qc1, height |-> h]
        
        GETLEADER ==  "a1" \* FROB - should select fro Acceptor set
        
        (* bend extends bstart => TRUE iff bend has an ancestor (parent) in common with bstart *)
        Extends(bstart, bend) ==  TRUE \* TODO
        
        Range(T) == { T[x] : x \in DOMAIN T }
    }

    macro SendNewView(to, qc) {
        newViewChannel[to] := Append(newViewChannel[to], <<[ type |-> "newview", 
                                     viewnum |-> curView[self], 
                                     node |-> EmptyNode, 
                                     justify |-> qc ],
                                     sig |-> self >>);
    }
    
    macro ReceiveNewView(m) {
        await newViewChannel[self] /= << >>;
            m := Head(newViewChannel[self]);
            newViewChannel[self] := Tail(newViewChannel[self]);   
    }
    
    macro SendVoteMsg(to, n) {
        voteChannel[to] := Append(voteChannel[to], <<[ type |-> "generic", 
                                  viewnum |-> curView[self], 
                                  node |-> n, 
                                  justify |-> {}, \* FIXME ???
                                  sig |-> 1 ]>>); \* FIXME ???
    }
    
    macro ReceiveVote(m){
        await voteChannel[self] /= << >>;
            m := Head(voteChannel[self]);
            voteChannel[self] := Tail(voteChannel[self]);   
    }
    
    macro BroadcastProposal(n) {
        proposalChannel := Append(
                                    <<[ type |-> "generic", 
                                    viewnum |-> curView[self], 
                                    node |-> n, 
                                    justify |-> {},
                                    sig |-> self ]>>,
                                    proposalChannel
                                    );
    }
    
    macro ReceiveProposal(m, lr){
        await Len(proposalChannel) > lr;
            m := Head(proposalChannel);           
    }
    
    macro PMUpdateQCHigh(qcphigh) {
        if (qcphigh.node.height > qchigh[self].node.height) {
            qchigh[self] := qcphigh;
            bleaf[self] := qchigh[self].node;
        };
    }
    
    macro EXECUTE(b) {
        Ledger[self] := Append(Ledger[self], << b.cmd >>);
        print<<"----------------> Ledger := ", Ledger[self]>>;
    }
    
    macro DoNextEvent() {
        await nextEventFlag[self] = TRUE /\ nextEventLOCK[self] = FALSE;
            nextEventFlag[self] := FALSE;
            call PMOnBeat("loop");
    }
    
    macro JustifyNode(bRet, b){ 
        bRet := b.justify.node;
    } 
   
    macro PMOnNextSyncView() {   \* not currently tested
        SendNewView(GETLEADER(), qchigh[self]);
    } 
    
    macro PMOnReceiveNewView() { \* not currently tested
        ReceiveNewView(mnew[self]);
        PMUpdateQCHigh(mnew[self].justify);
        curView[self] := curView[self] + 1;
    }

    procedure OnPropose(bpropose, c, qch) {
        onp1:
            bpropose := CreateLeaf(bpropose, c, qch, (bpropose.height + 1));
            BroadcastProposal(bpropose);
        onp_return:
            return;
    }
      
    procedure OnReceiveProposal() {
        orp1:
            ReceiveProposal(mprop[self], lastReadProposal[self]);
            lastReadProposal[self] := lastReadProposal[self] + 1;
            
            if ((mprop[self].node.height > vheight[self] /\ Extends(mprop[self].node, block[self]) )
                \/ mprop[self].node.justify.node.height > block[self].height ) {
                    vheight[self] := mprop[self].node.height;
                    SendVoteMsg(GETLEADER, mprop[self].node);
            };
            call Update(mprop[self].node);
        orp_return:
            return; 
    }
    
   
    procedure PMOnBeat(debug) 
    variables tmp
    {
        pmob1:  
            if (self = GETLEADER) {        
                        tmp := NextValue(sentValues);
                        call OnPropose(bleaf[self], tmp, qchigh[self]);
        pmob2:
                        sentValues := sentValues \cup {tmp};
            };
        pmob_return:
            return;
    }
    
    procedure MakeQC(vb) { 
        \* vb is a set {[ votemessage ], ... } for node b -   FIXME
        mqc1: 
            qc[self] := [ viewnum |->  vb.justify.viewnum,  \* FIXME
                          node    |->  vb, 
                          sig     |->  vb.justify.sig ];    \* FIXME - maybe better as a set of sigs as per paper
        mcq_return:
            return; \* return in qc[self]
    }
    
    procedure AddItemToV(key, val) {
        aitv1:
            if ( key \in DOMAIN V[self] )
                VEntry[self] := V[self][key]; 
            else
                VEntry[self] := {};
        aitv2: 
            VEntry[self] := VEntry[self] \cup {val};
            V[self] := [x \in DOMAIN V[self] \cup {key} |-> VEntry[self] ] @@ V[self];
            
            \*print<<"V[key] = ", V[self][key]>>;
            return;     
    }
    
    procedure OnReceiveVote() { 
        orv1:
            nextEventLOCK[self] := TRUE;

            ReceiveVote(mvote[self]);
        orv2:   
            call AddItemToV(mvote[self][1].node, mvote[self][1]);
        orv3:
        	(***************************************************************)
            (* Since we cannot use threshold signatures in TLA+, we just   *)
            (* count votes.                                                *)
            (***************************************************************)
            if (Cardinality(V[self][mvote[self][1].node]) >= Cardinality(Acceptor) - Cardinality(FakeAcceptor) ) { \* (n - f)
        orv4:
                call MakeQC( mvote[self][1].node );
        orv5:
                PMUpdateQCHigh(qc[self]);     
            };
        orv_return:
            nextEventLOCK[self] := FALSE;
            return;
    }
      
    procedure OnCommit(node) {
        oc1:
            (***********************************************************)
            (* In the HotSuff algorithm 4. we would recursively        *)
            (* call OnCommit(node.parent) here, but unfortunately      *)
            (* TLA+ does not allow recursive procedure calls, so       *)
            (* we do the following -                                   *)
            (***********************************************************)   
            if (bexec[self].height < node.height) {
                \* SIMULATED RECURSION with node.parent
                if(bexec[self].height < node.parent[1][1].height) {
                    \* recurse again ????
                    if (node.parent[1][1].parent[1][1] # genesis_null) {
                        if (bexec[self].height < node.parent[1][1].parent[1][1]) {
                            print<<"oc: second recursion">>;
                        };
                    };
                    EXECUTE(node.parent[1][1]);
                    nextEventFlag[self] := TRUE;
                };
            };
        oc_return:
            return;
    }
    
    procedure Update(bstar) {
    (***************************************************************************)
    (* Called whenever a proposal is received, whether it is voted for or not  *)
    (***************************************************************************)       
        u1:
            nextEventLOCK[self] := TRUE;
        u2:    
            JustifyNode(bpp[self], bstar);
        u3:
            JustifyNode(bp[self],  bpp[self]);      
        u4:         
            JustifyNode(b[self],    bp[self]);
        u5:   
            PMUpdateQCHigh(bstar.justify);  \* pre-commit-phase on bpp
        u6:   
            if (bp[self].height > block[self].height) {
                block[self] := bp[self];    \* commit-phase on bp
            } else {
                goto u_return;
            };
        u8:    
            if (bpp[self].parent[1][1] = bp[self] 
                  /\ bp[self].parent[1][1] = b[self])
            {                    
                call OnCommit(b[self]);
        u9:
                bexec[self] := b[self];     \* decide-phase on b
            };
        u_return:
            nextEventLOCK[self] := FALSE;
            return;
    }

(***************************************************************************)
(* We now start a process for each Acceptor.                               *)
(***************************************************************************)
    process (a \in ByzAcceptor) {  
        p1:  
            sentValues := {};  
                   
            \* would have been set in orp:
            vheight[self] := b0.height;
             
            \* would have been set in pmob:      
            bleaf[self] := b0;
            
            \* would have been set in orv:         
        p2: 
            qchigh[self] := [ viewnum |-> 0,
                              node |-> b0,
                              sig |-> 1 
                            ];
                            
            \* these would have been set in u:
            block[self] := genesis_bpp; 
            bexec[self] := genesis_null;
            
            \* genesis_null is implicitly stored on the ledger
            
            call PMOnBeat("p2"); \* propose the first real cmd

        loop:    
            while(TRUE) {         
        p3:               
                either call OnReceiveVote()
                or receiveprop: call OnReceiveProposal()
                or nextevent: DoNextEvent()   
                \*or PMOnReceiveNewView() \* not tested
            };
    }
}
**)
=============================================================================
\* Modification History
\* Last modified Sat Mar 07 15:31:15 GMT 2020 by steve
\* Created Thu Feb 20 12:24:16 GMT 2020 by steve
