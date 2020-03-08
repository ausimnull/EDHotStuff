----------------------------- MODULE EDHotStuff -----------------------------
 EXTENDS Integers, Sequences, FiniteSets, TLC
 
 (**************************************************************************)
 (*                                                                        *)
 (*                             VERSION 0.2                                *)
 (*                                                                        *)
 (* This module is a specification based on Algorithms 4, and 5, in the    *)
 (* HotSuff white paper. In as much as is possible it uses the same        *)
 (* notation as the published algorithms. There are several parts that     *)
 (* are implementation dependent, namely how the parent chains are         *)
 (* implemented, and how leaders are selected. I have chosen the simplest  *)
 (* possible implemetations in this version.                               *)
 (*                                                                        *)
 (* No attempt has been made yet to define any invariants                  *)
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

(***************************************************************************)
(* The following are all macros which get substituted in-line in the code. *)
(* This is done to make the code readable but without the overhead of      *)
(* calling a procedure.                                                    *)
(* There lots of commented out print statements that are useful for        *)
(* debuggering.                                                            *)
(*                                                                         *)
(***************************************************************************)
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
        \* vb is a set { [ votemessage ], ... } for node b  FIXME
        xxxxxxx:
            print<<"mqch: making QC from ", vb.cmd>>;
        mqc1: 
            qc[self] := [ viewnum |->  vb.justify.viewnum, \* FROB
                          node    |->  vb, 
                          sig     |->  vb.justify.sig ]; \* FROB - maybe better as a set of sigs as per paper
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
            print<<"orv: got vote msg for ", mvote[self][1].node.cmd>>;
            goto orv4; \* ********** !!
        orv2:
            \* avoid duplicates
            if ( mvote[self][1] \in V[self][mvote[self][1].node] ) {
                goto orv_return;
            };
        orv3:   
            call AddItemToV(mvote[self][1].node, mvote[self][1]);
        orv4:
            if (mvote[self][1].sig <= Cardinality(Acceptor) - Cardinality(FakeAcceptor) ) { \* (n - f)
        orv4a:
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

(*
<<"pmob: called from ", "p2">>
<<"pmob: proposing ", "v1">>
<<"pmob: qchigh", "b0">>
<<"onp: parent = ", "v1">>
<<"onp: bleaf = ", "b0">>
<<"orp: processing ", "v1">>
<<"orp: proposal height = ", 5>>
<<"orp: vheight = ", 4>>
<<"orp: proposal.justify.node.height", 4>>
<<"orp: block.height", 1>>
<<"orp: voting for received proposal ", "v1">>
<<"u: bstar cmd = ", "v1", " height = ", 5>>
<<"u: bpp cmd =", "b0", " height = ", 4>>
<<"u: bp  cmd = ", "genesis_b", " height = ", 3>>
<<"u: b   cmd = ", "genesis_bp", " height = ", 2>>
<<"u: block = ", "genesis_bpp", " height = ", 1>>
<<"u: pre-commit phase on ", "b0">>
<<"pmuqch: qcphigh ", 4>>
<<"pmuqch: qphigh  = ", 4>>
<<"u: commit phase on ", "genesis_b">>
<<"u: updating block to  ", "genesis_b", " height = ", 3>>
<<"u: decide phase on ", "genesis_bp">>
<<"oc: got ", "genesis_bp">>
<<"oc: trying to execute ", "genesis_bpp">>
<<"oc: recursively calling using node.parent">>
<<"oc: node.parent.height = ", 1>>
<<"oc: committing ", "genesis_bpp">>
<<"----------------> Ledger := ", <<<<"genesis_bpp">>>>>>
<<"orv: got vote msg for ", "v1">>
<<"orp: processing ", "v1">>
<<"orv: QUORUM REACHED on ", "v1">>
<<"orp: proposal height = ", 5>>
<<"orv: woogle">>
<<"orp: vheight = ", 5>>
<<"orp: proposal.justify.node.height", 4>>
<<"orp: block.height", 3>>
<<"orp: voting for received proposal ", "v1">>
<<"pmob: called from ", "loop">>
<<"u: bstar cmd = ", "v1", " height = ", 5>>
<<"mqch: making QC from ", "v1">>
<<"u: bpp cmd =", "b0", " height = ", 4>>
<<"u: bp  cmd = ", "genesis_b", " height = ", 3>>
<<"orv: updating QCHigh to ", "v1">>
<<"pmuqch: qcphigh ", 5>>
<<"pmuqch: qphigh  = ", 4>>
<<"pmuqch: updating qchigh to ", "v1">>
<<"pmuqch: updating bleaf to ", "v1">>
<<"u: b   cmd = ", "genesis_bp", " height = ", 2>>
<<"u: block = ", "genesis_b", " height = ", 3>>
<<"u: pre-commit phase on ", "b0">>
<<"pmob: called from ", "p2">>
<<"pmob: proposing ", "v1">>
<<"pmob: qchigh", "b0">>
<<"orv: return">>
<<"onp: parent = ", "v1">>
<<"onp: bleaf = ", "b0">>
<<"pmuqch: qcphigh ", 4>>
<<"pmuqch: qphigh  = ", 4>>
<<"u: -----> no commit-phase on ", "genesis_b">>
<<"pmob: called from ", "loop">>
<<"orp: processing ", "v1">>
<<"orp: processing ", "v1">>
<<"orp: proposal height = ", 5>>
<<"orp: proposal height = ", 5>>
<<"orp: vheight = ", 4>>
<<"orp: vheight = ", 5>>
<<"orp: proposal.justify.node.height", 4>>
<<"orp: proposal.justify.node.height", 4>>
<<"orp: block.height", 1>>
<<"orp: block.height", 3>>
<<"orp: voting for received proposal ", "v1">>
<<"orp: voting for received proposal ", "v1">>
<<"u: bstar cmd = ", "v1", " height = ", 5>>
<<"orv: got vote msg for ", "v1">>
<<"u: bpp cmd =", "b0", " height = ", 4>>
<<"orv: QUORUM REACHED on ", "v1">>
<<"orv: woogle">>
<<"u: bp  cmd = ", "genesis_b", " height = ", 3>>
<<"pmob: called from ", "loop">>
<<"u: bstar cmd = ", "v1", " height = ", 5>>
<<"u: b   cmd = ", "genesis_bp", " height = ", 2>>
<<"u: block = ", "genesis_bpp", " height = ", 1>>
<<"u: pre-commit phase on ", "b0">>
<<"mqch: making QC from ", "v1">>
<<"pmuqch: qcphigh ", 4>>
<<"pmuqch: qphigh  = ", 4>>
<<"u: bpp cmd =", "b0", " height = ", 4>>
<<"u: commit phase on ", "genesis_b">>
<<"u: updating block to  ", "genesis_b", " height = ", 3>>
<<"u: decide phase on ", "genesis_bp">>
<<"u: bp  cmd = ", "genesis_b", " height = ", 3>>
<<"orv: updating QCHigh to ", "v1">>
<<"pmuqch: qcphigh ", 5>>
<<"pmuqch: qphigh  = ", 4>>
<<"pmuqch: updating qchigh to ", "v1">>
<<"pmuqch: updating bleaf to ", "v1">>
<<"oc: got ", "genesis_bp">>
<<"u: b   cmd = ", "genesis_bp", " height = ", 2>>
<<"u: block = ", "genesis_b", " height = ", 3>>
<<"u: pre-commit phase on ", "b0">>
<<"orv: return">>
<<"oc: trying to execute ", "genesis_bpp">>
<<"oc: recursively calling using node.parent">>
<<"oc: node.parent.height = ", 1>>
<<"oc: committing ", "genesis_bpp">>
<<"----------------> Ledger := ", <<<<"genesis_bpp">>>>>>
<<"pmuqch: qcphigh ", 4>>
<<"pmuqch: qphigh  = ", 5>>
<<"u: -----> no commit-phase on ", "genesis_b">>
<<"orv: got vote msg for ", "v1">>
<<"orv: QUORUM REACHED on ", "v1">>
<<"orv: woogle">>
<<"pmob: called from ", "loop">>
<<"mqch: making QC from ", "v1">>
<<"orv: updating QCHigh to ", "v1">>
<<"pmuqch: qcphigh ", 5>>
<<"pmuqch: qphigh  = ", 5>>
<<"orv: return">>
<<"pmob: called from ", "loop">>
<<"pmob: called from ", "loop">>

*)

****)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES Ledger, sentValues, voteChannel, newViewChannel, proposalChannel, 
          lastReadProposal, vheight, block, bexec, qchigh, bleaf, curView, V, 
          b, bp, bpp, nextEventFlag, nextEventLOCK, qc, mvote, mprop, mnew, 
          VEntry, pc, stack

(* define statement *)
CreateLeaf(p, v2, qc1, h) == [parent |-> p, cmd |-> v2, justify |-> qc1, height |-> h]

GETLEADER ==  "a1"


Extends(bstart, bend) ==  TRUE

Range(T) == { T[x] : x \in DOMAIN T }

VARIABLES bpropose, c, qch, debug, tmp, vb, key, val, node, bstar

vars == << Ledger, sentValues, voteChannel, newViewChannel, proposalChannel, 
           lastReadProposal, vheight, block, bexec, qchigh, bleaf, curView, V, 
           b, bp, bpp, nextEventFlag, nextEventLOCK, qc, mvote, mprop, mnew, 
           VEntry, pc, stack, bpropose, c, qch, debug, tmp, vb, key, val, 
           node, bstar >>

ProcSet == (ByzAcceptor)

Init == (* Global variables *)
        /\ Ledger = [a \in Acceptor |-> << >>]
        /\ sentValues = {}
        /\ voteChannel = [a \in Acceptor |-> << >>]
        /\ newViewChannel = [a \in Acceptor |-> << >>]
        /\ proposalChannel = << >>
        /\ lastReadProposal = [a \in Acceptor |-> 0]
        /\ vheight = [a \in Acceptor |-> 0]
        /\ block = [a \in Acceptor |-> EmptyNode]
        /\ bexec = [a \in Acceptor |-> EmptyNode]
        /\ qchigh = [a \in Acceptor |-> << >>]
        /\ bleaf = [a \in Acceptor |-> EmptyNode]
        /\ curView = [a \in Acceptor |-> 0]
        /\ V = [a \in Acceptor |-> EmptyV]
        /\ b = [a \in Acceptor |-> EmptyNode]
        /\ bp = [a \in Acceptor |-> EmptyNode]
        /\ bpp = [a \in Acceptor |-> EmptyNode]
        /\ nextEventFlag = [a \in Acceptor |-> FALSE]
        /\ nextEventLOCK = [a \in Acceptor |-> FALSE]
        /\ qc = [a \in Acceptor |-> << >>]
        /\ mvote = [a \in Acceptor |-> << >>]
        /\ mprop = [a \in Acceptor |-> << >>]
        /\ mnew = [a \in Acceptor |-> << >>]
        /\ VEntry = [a \in Acceptor |-> {}]
        (* Procedure OnPropose *)
        /\ bpropose = [ self \in ProcSet |-> defaultInitValue]
        /\ c = [ self \in ProcSet |-> defaultInitValue]
        /\ qch = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure PMOnBeat *)
        /\ debug = [ self \in ProcSet |-> defaultInitValue]
        /\ tmp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure MakeQC *)
        /\ vb = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure AddItemToV *)
        /\ key = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure OnCommit *)
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Update *)
        /\ bstar = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p1"]

onp1(self) == /\ pc[self] = "onp1"
              /\ bpropose' = [bpropose EXCEPT ![self] = CreateLeaf(bpropose[self], c[self], qch[self], (bpropose[self].height + 1))]
              /\ proposalChannel' = Append(
                                             <<[ type |-> "generic",
                                             viewnum |-> curView[self],
                                             node |-> bpropose'[self],
                                             justify |-> {},
                                             sig |-> self ]>>,
                                             proposalChannel
                                             )
              /\ pc' = [pc EXCEPT ![self] = "onp_return"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              lastReadProposal, vheight, block, bexec, qchigh, 
                              bleaf, curView, V, b, bp, bpp, nextEventFlag, 
                              nextEventLOCK, qc, mvote, mprop, mnew, VEntry, 
                              stack, c, qch, debug, tmp, vb, key, val, node, 
                              bstar >>

onp_return(self) == /\ pc[self] = "onp_return"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ bpropose' = [bpropose EXCEPT ![self] = Head(stack[self]).bpropose]
                    /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
                    /\ qch' = [qch EXCEPT ![self] = Head(stack[self]).qch]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                    newViewChannel, proposalChannel, 
                                    lastReadProposal, vheight, block, bexec, 
                                    qchigh, bleaf, curView, V, b, bp, bpp, 
                                    nextEventFlag, nextEventLOCK, qc, mvote, 
                                    mprop, mnew, VEntry, debug, tmp, vb, key, 
                                    val, node, bstar >>

OnPropose(self) == onp1(self) \/ onp_return(self)

orp1(self) == /\ pc[self] = "orp1"
              /\ Len(proposalChannel) > (lastReadProposal[self])
              /\ mprop' = [mprop EXCEPT ![self] = Head(proposalChannel)]
              /\ lastReadProposal' = [lastReadProposal EXCEPT ![self] = lastReadProposal[self] + 1]
              /\ IF (mprop'[self].node.height > vheight[self] /\ Extends(mprop'[self].node, block[self]) )
                    \/ mprop'[self].node.justify.node.height > block[self].height
                    THEN /\ vheight' = [vheight EXCEPT ![self] = mprop'[self].node.height]
                         /\ voteChannel' = [voteChannel EXCEPT ![GETLEADER] = Append(voteChannel[GETLEADER], <<[ type |-> "generic",
                                                                                     viewnum |-> curView[self],
                                                                                     node |-> (mprop'[self].node),
                                                                                     justify |-> {},
                                                                                     sig |-> 1 ]>>)]
                    ELSE /\ TRUE
                         /\ UNCHANGED << voteChannel, vheight >>
              /\ /\ bstar' = [bstar EXCEPT ![self] = mprop'[self].node]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Update",
                                                          pc        |->  "orp_return",
                                                          bstar     |->  bstar[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "u1"]
              /\ UNCHANGED << Ledger, sentValues, newViewChannel, 
                              proposalChannel, block, bexec, qchigh, bleaf, 
                              curView, V, b, bp, bpp, nextEventFlag, 
                              nextEventLOCK, qc, mvote, mnew, VEntry, bpropose, 
                              c, qch, debug, tmp, vb, key, val, node >>

orp_return(self) == /\ pc[self] = "orp_return"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                    newViewChannel, proposalChannel, 
                                    lastReadProposal, vheight, block, bexec, 
                                    qchigh, bleaf, curView, V, b, bp, bpp, 
                                    nextEventFlag, nextEventLOCK, qc, mvote, 
                                    mprop, mnew, VEntry, bpropose, c, qch, 
                                    debug, tmp, vb, key, val, node, bstar >>

OnReceiveProposal(self) == orp1(self) \/ orp_return(self)

pmob1(self) == /\ pc[self] = "pmob1"
               /\ IF self = GETLEADER
                     THEN /\ tmp' = [tmp EXCEPT ![self] = NextValue(sentValues)]
                          /\ /\ bpropose' = [bpropose EXCEPT ![self] = bleaf[self]]
                             /\ c' = [c EXCEPT ![self] = tmp'[self]]
                             /\ qch' = [qch EXCEPT ![self] = qchigh[self]]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "OnPropose",
                                                                      pc        |->  "pmob2",
                                                                      bpropose  |->  bpropose[self],
                                                                      c         |->  c[self],
                                                                      qch       |->  qch[self] ] >>
                                                                  \o stack[self]]
                          /\ pc' = [pc EXCEPT ![self] = "onp1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "pmob_return"]
                          /\ UNCHANGED << stack, bpropose, c, qch, tmp >>
               /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                               proposalChannel, lastReadProposal, vheight, 
                               block, bexec, qchigh, bleaf, curView, V, b, bp, 
                               bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                               mprop, mnew, VEntry, debug, vb, key, val, node, 
                               bstar >>

pmob2(self) == /\ pc[self] = "pmob2"
               /\ sentValues' = (sentValues \cup {tmp[self]})
               /\ pc' = [pc EXCEPT ![self] = "pmob_return"]
               /\ UNCHANGED << Ledger, voteChannel, newViewChannel, 
                               proposalChannel, lastReadProposal, vheight, 
                               block, bexec, qchigh, bleaf, curView, V, b, bp, 
                               bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                               mprop, mnew, VEntry, stack, bpropose, c, qch, 
                               debug, tmp, vb, key, val, node, bstar >>

pmob_return(self) == /\ pc[self] = "pmob_return"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ tmp' = [tmp EXCEPT ![self] = Head(stack[self]).tmp]
                     /\ debug' = [debug EXCEPT ![self] = Head(stack[self]).debug]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                     newViewChannel, proposalChannel, 
                                     lastReadProposal, vheight, block, bexec, 
                                     qchigh, bleaf, curView, V, b, bp, bpp, 
                                     nextEventFlag, nextEventLOCK, qc, mvote, 
                                     mprop, mnew, VEntry, bpropose, c, qch, vb, 
                                     key, val, node, bstar >>

PMOnBeat(self) == pmob1(self) \/ pmob2(self) \/ pmob_return(self)

xxxxxxx(self) == /\ pc[self] = "xxxxxxx"
                 /\ PrintT(<<"mqch: making QC from ", vb[self].cmd>>)
                 /\ pc' = [pc EXCEPT ![self] = "mqc1"]
                 /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                 newViewChannel, proposalChannel, 
                                 lastReadProposal, vheight, block, bexec, 
                                 qchigh, bleaf, curView, V, b, bp, bpp, 
                                 nextEventFlag, nextEventLOCK, qc, mvote, 
                                 mprop, mnew, VEntry, stack, bpropose, c, qch, 
                                 debug, tmp, vb, key, val, node, bstar >>

mqc1(self) == /\ pc[self] = "mqc1"
              /\ qc' = [qc EXCEPT ![self] = [ viewnum |->  vb[self].justify.viewnum,
                                              node    |->  vb[self],
                                              sig     |->  vb[self].justify.sig ]]
              /\ pc' = [pc EXCEPT ![self] = "mcq_return"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, nextEventLOCK, mvote, mprop, 
                              mnew, VEntry, stack, bpropose, c, qch, debug, 
                              tmp, vb, key, val, node, bstar >>

mcq_return(self) == /\ pc[self] = "mcq_return"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ vb' = [vb EXCEPT ![self] = Head(stack[self]).vb]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                    newViewChannel, proposalChannel, 
                                    lastReadProposal, vheight, block, bexec, 
                                    qchigh, bleaf, curView, V, b, bp, bpp, 
                                    nextEventFlag, nextEventLOCK, qc, mvote, 
                                    mprop, mnew, VEntry, bpropose, c, qch, 
                                    debug, tmp, key, val, node, bstar >>

MakeQC(self) == xxxxxxx(self) \/ mqc1(self) \/ mcq_return(self)

aitv1(self) == /\ pc[self] = "aitv1"
               /\ IF key[self] \in DOMAIN V[self]
                     THEN /\ VEntry' = [VEntry EXCEPT ![self] = V[self][key[self]]]
                     ELSE /\ VEntry' = [VEntry EXCEPT ![self] = {}]
               /\ pc' = [pc EXCEPT ![self] = "aitv2"]
               /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                               proposalChannel, lastReadProposal, vheight, 
                               block, bexec, qchigh, bleaf, curView, V, b, bp, 
                               bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                               mprop, mnew, stack, bpropose, c, qch, debug, 
                               tmp, vb, key, val, node, bstar >>

aitv2(self) == /\ pc[self] = "aitv2"
               /\ VEntry' = [VEntry EXCEPT ![self] = VEntry[self] \cup {val[self]}]
               /\ V' = [V EXCEPT ![self] = [x \in DOMAIN V[self] \cup {key[self]} |-> VEntry'[self] ] @@ V[self]]
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ key' = [key EXCEPT ![self] = Head(stack[self]).key]
               /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                               proposalChannel, lastReadProposal, vheight, 
                               block, bexec, qchigh, bleaf, curView, b, bp, 
                               bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                               mprop, mnew, bpropose, c, qch, debug, tmp, vb, 
                               node, bstar >>

AddItemToV(self) == aitv1(self) \/ aitv2(self)

orv1(self) == /\ pc[self] = "orv1"
              /\ nextEventLOCK' = [nextEventLOCK EXCEPT ![self] = TRUE]
              /\ voteChannel[self] /= << >>
              /\ mvote' = [mvote EXCEPT ![self] = Head(voteChannel[self])]
              /\ voteChannel' = [voteChannel EXCEPT ![self] = Tail(voteChannel[self])]
              /\ PrintT(<<"orv: got vote msg for ", mvote'[self][1].node.cmd>>)
              /\ pc' = [pc EXCEPT ![self] = "orv4"]
              /\ UNCHANGED << Ledger, sentValues, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, qc, mprop, mnew, VEntry, 
                              stack, bpropose, c, qch, debug, tmp, vb, key, 
                              val, node, bstar >>

orv2(self) == /\ pc[self] = "orv2"
              /\ IF mvote[self][1] \in V[self][mvote[self][1].node]
                    THEN /\ pc' = [pc EXCEPT ![self] = "orv_return"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "orv3"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                              mprop, mnew, VEntry, stack, bpropose, c, qch, 
                              debug, tmp, vb, key, val, node, bstar >>

orv3(self) == /\ pc[self] = "orv3"
              /\ /\ key' = [key EXCEPT ![self] = mvote[self][1].node]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "AddItemToV",
                                                          pc        |->  "orv4",
                                                          key       |->  key[self],
                                                          val       |->  val[self] ] >>
                                                      \o stack[self]]
                 /\ val' = [val EXCEPT ![self] = mvote[self][1]]
              /\ pc' = [pc EXCEPT ![self] = "aitv1"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                              mprop, mnew, VEntry, bpropose, c, qch, debug, 
                              tmp, vb, node, bstar >>

orv4(self) == /\ pc[self] = "orv4"
              /\ IF mvote[self][1].sig <= Cardinality(Acceptor) - Cardinality(FakeAcceptor)
                    THEN /\ pc' = [pc EXCEPT ![self] = "orv4a"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "orv_return"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                              mprop, mnew, VEntry, stack, bpropose, c, qch, 
                              debug, tmp, vb, key, val, node, bstar >>

orv4a(self) == /\ pc[self] = "orv4a"
               /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "MakeQC",
                                                           pc        |->  "orv5",
                                                           vb        |->  vb[self] ] >>
                                                       \o stack[self]]
                  /\ vb' = [vb EXCEPT ![self] = mvote[self][1].node]
               /\ pc' = [pc EXCEPT ![self] = "xxxxxxx"]
               /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                               proposalChannel, lastReadProposal, vheight, 
                               block, bexec, qchigh, bleaf, curView, V, b, bp, 
                               bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                               mprop, mnew, VEntry, bpropose, c, qch, debug, 
                               tmp, key, val, node, bstar >>

orv5(self) == /\ pc[self] = "orv5"
              /\ IF (qc[self]).node.height > qchigh[self].node.height
                    THEN /\ qchigh' = [qchigh EXCEPT ![self] = qc[self]]
                         /\ bleaf' = [bleaf EXCEPT ![self] = qchigh'[self].node]
                    ELSE /\ TRUE
                         /\ UNCHANGED << qchigh, bleaf >>
              /\ pc' = [pc EXCEPT ![self] = "orv_return"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, curView, V, b, bp, bpp, 
                              nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                              mnew, VEntry, stack, bpropose, c, qch, debug, 
                              tmp, vb, key, val, node, bstar >>

orv_return(self) == /\ pc[self] = "orv_return"
                    /\ nextEventLOCK' = [nextEventLOCK EXCEPT ![self] = FALSE]
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                    newViewChannel, proposalChannel, 
                                    lastReadProposal, vheight, block, bexec, 
                                    qchigh, bleaf, curView, V, b, bp, bpp, 
                                    nextEventFlag, qc, mvote, mprop, mnew, 
                                    VEntry, bpropose, c, qch, debug, tmp, vb, 
                                    key, val, node, bstar >>

OnReceiveVote(self) == orv1(self) \/ orv2(self) \/ orv3(self) \/ orv4(self)
                          \/ orv4a(self) \/ orv5(self) \/ orv_return(self)

oc1(self) == /\ pc[self] = "oc1"
             /\ IF bexec[self].height < node[self].height
                   THEN /\ IF bexec[self].height < node[self].parent[1][1].height
                              THEN /\ IF node[self].parent[1][1].parent[1][1] # genesis_null
                                         THEN /\ IF bexec[self].height < node[self].parent[1][1].parent[1][1]
                                                    THEN /\ PrintT(<<"oc: second recursion">>)
                                                    ELSE /\ TRUE
                                         ELSE /\ TRUE
                                   /\ Ledger' = [Ledger EXCEPT ![self] = Append(Ledger[self], << (node[self].parent[1][1]).cmd >>)]
                                   /\ PrintT(<<"----------------> Ledger := ", Ledger'[self]>>)
                                   /\ nextEventFlag' = [nextEventFlag EXCEPT ![self] = TRUE]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << Ledger, nextEventFlag >>
                   ELSE /\ TRUE
                        /\ UNCHANGED << Ledger, nextEventFlag >>
             /\ pc' = [pc EXCEPT ![self] = "oc_return"]
             /\ UNCHANGED << sentValues, voteChannel, newViewChannel, 
                             proposalChannel, lastReadProposal, vheight, block, 
                             bexec, qchigh, bleaf, curView, V, b, bp, bpp, 
                             nextEventLOCK, qc, mvote, mprop, mnew, VEntry, 
                             stack, bpropose, c, qch, debug, tmp, vb, key, val, 
                             node, bstar >>

oc_return(self) == /\ pc[self] = "oc_return"
                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                   /\ node' = [node EXCEPT ![self] = Head(stack[self]).node]
                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                   newViewChannel, proposalChannel, 
                                   lastReadProposal, vheight, block, bexec, 
                                   qchigh, bleaf, curView, V, b, bp, bpp, 
                                   nextEventFlag, nextEventLOCK, qc, mvote, 
                                   mprop, mnew, VEntry, bpropose, c, qch, 
                                   debug, tmp, vb, key, val, bstar >>

OnCommit(self) == oc1(self) \/ oc_return(self)

u1(self) == /\ pc[self] = "u1"
            /\ nextEventLOCK' = [nextEventLOCK EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "u2"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, b, bp, bpp, 
                            nextEventFlag, qc, mvote, mprop, mnew, VEntry, 
                            stack, bpropose, c, qch, debug, tmp, vb, key, val, 
                            node, bstar >>

u2(self) == /\ pc[self] = "u2"
            /\ bpp' = [bpp EXCEPT ![self] = bstar[self].justify.node]
            /\ pc' = [pc EXCEPT ![self] = "u3"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, b, bp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, stack, bpropose, c, qch, debug, tmp, 
                            vb, key, val, node, bstar >>

u3(self) == /\ pc[self] = "u3"
            /\ bp' = [bp EXCEPT ![self] = (bpp[self]).justify.node]
            /\ pc' = [pc EXCEPT ![self] = "u4"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, b, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, stack, bpropose, c, qch, debug, tmp, 
                            vb, key, val, node, bstar >>

u4(self) == /\ pc[self] = "u4"
            /\ b' = [b EXCEPT ![self] = (bp[self]).justify.node]
            /\ pc' = [pc EXCEPT ![self] = "u5"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, bp, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, stack, bpropose, c, qch, debug, tmp, 
                            vb, key, val, node, bstar >>

u5(self) == /\ pc[self] = "u5"
            /\ IF (bstar[self].justify).node.height > qchigh[self].node.height
                  THEN /\ qchigh' = [qchigh EXCEPT ![self] = bstar[self].justify]
                       /\ bleaf' = [bleaf EXCEPT ![self] = qchigh'[self].node]
                  ELSE /\ TRUE
                       /\ UNCHANGED << qchigh, bleaf >>
            /\ pc' = [pc EXCEPT ![self] = "u6"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, curView, V, b, bp, bpp, nextEventFlag, 
                            nextEventLOCK, qc, mvote, mprop, mnew, VEntry, 
                            stack, bpropose, c, qch, debug, tmp, vb, key, val, 
                            node, bstar >>

u6(self) == /\ pc[self] = "u6"
            /\ IF bp[self].height > block[self].height
                  THEN /\ block' = [block EXCEPT ![self] = bp[self]]
                       /\ pc' = [pc EXCEPT ![self] = "u8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "u_return"]
                       /\ block' = block
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, bexec, 
                            qchigh, bleaf, curView, V, b, bp, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, stack, bpropose, c, qch, debug, tmp, 
                            vb, key, val, node, bstar >>

u8(self) == /\ pc[self] = "u8"
            /\ IF bpp[self].parent[1][1] = bp[self]
                    /\ bp[self].parent[1][1] = b[self]
                  THEN /\ /\ node' = [node EXCEPT ![self] = b[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "OnCommit",
                                                                   pc        |->  "u9",
                                                                   node      |->  node[self] ] >>
                                                               \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "oc1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "u_return"]
                       /\ UNCHANGED << stack, node >>
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, b, bp, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, bpropose, c, qch, debug, tmp, vb, 
                            key, val, bstar >>

u9(self) == /\ pc[self] = "u9"
            /\ bexec' = [bexec EXCEPT ![self] = b[self]]
            /\ pc' = [pc EXCEPT ![self] = "u_return"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            qchigh, bleaf, curView, V, b, bp, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, stack, bpropose, c, qch, debug, tmp, 
                            vb, key, val, node, bstar >>

u_return(self) == /\ pc[self] = "u_return"
                  /\ nextEventLOCK' = [nextEventLOCK EXCEPT ![self] = FALSE]
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ bstar' = [bstar EXCEPT ![self] = Head(stack[self]).bstar]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                  newViewChannel, proposalChannel, 
                                  lastReadProposal, vheight, block, bexec, 
                                  qchigh, bleaf, curView, V, b, bp, bpp, 
                                  nextEventFlag, qc, mvote, mprop, mnew, 
                                  VEntry, bpropose, c, qch, debug, tmp, vb, 
                                  key, val, node >>

Update(self) == u1(self) \/ u2(self) \/ u3(self) \/ u4(self) \/ u5(self)
                   \/ u6(self) \/ u8(self) \/ u9(self) \/ u_return(self)

p1(self) == /\ pc[self] = "p1"
            /\ sentValues' = {}
            /\ vheight' = [vheight EXCEPT ![self] = b0.height]
            /\ bleaf' = [bleaf EXCEPT ![self] = b0]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << Ledger, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, block, bexec, 
                            qchigh, curView, V, b, bp, bpp, nextEventFlag, 
                            nextEventLOCK, qc, mvote, mprop, mnew, VEntry, 
                            stack, bpropose, c, qch, debug, tmp, vb, key, val, 
                            node, bstar >>

p2(self) == /\ pc[self] = "p2"
            /\ qchigh' = [qchigh EXCEPT ![self] = [ viewnum |-> 0,
                                                    node |-> b0,
                                                    sig |-> 1
                                                  ]]
            /\ block' = [block EXCEPT ![self] = genesis_bpp]
            /\ bexec' = [bexec EXCEPT ![self] = genesis_null]
            /\ /\ debug' = [debug EXCEPT ![self] = "p2"]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "PMOnBeat",
                                                        pc        |->  "loop",
                                                        tmp       |->  tmp[self],
                                                        debug     |->  debug[self] ] >>
                                                    \o stack[self]]
            /\ tmp' = [tmp EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "pmob1"]
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, bleaf, 
                            curView, V, b, bp, bpp, nextEventFlag, 
                            nextEventLOCK, qc, mvote, mprop, mnew, VEntry, 
                            bpropose, c, qch, vb, key, val, node, bstar >>

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "p3"]
              /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                              proposalChannel, lastReadProposal, vheight, 
                              block, bexec, qchigh, bleaf, curView, V, b, bp, 
                              bpp, nextEventFlag, nextEventLOCK, qc, mvote, 
                              mprop, mnew, VEntry, stack, bpropose, c, qch, 
                              debug, tmp, vb, key, val, node, bstar >>

p3(self) == /\ pc[self] = "p3"
            /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "OnReceiveVote",
                                                           pc        |->  "loop" ] >>
                                                       \o stack[self]]
                  /\ pc' = [pc EXCEPT ![self] = "orv1"]
               \/ /\ pc' = [pc EXCEPT ![self] = "receiveprop"]
                  /\ stack' = stack
               \/ /\ pc' = [pc EXCEPT ![self] = "nextevent"]
                  /\ stack' = stack
            /\ UNCHANGED << Ledger, sentValues, voteChannel, newViewChannel, 
                            proposalChannel, lastReadProposal, vheight, block, 
                            bexec, qchigh, bleaf, curView, V, b, bp, bpp, 
                            nextEventFlag, nextEventLOCK, qc, mvote, mprop, 
                            mnew, VEntry, bpropose, c, qch, debug, tmp, vb, 
                            key, val, node, bstar >>

receiveprop(self) == /\ pc[self] = "receiveprop"
                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "OnReceiveProposal",
                                                              pc        |->  "loop" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "orp1"]
                     /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                     newViewChannel, proposalChannel, 
                                     lastReadProposal, vheight, block, bexec, 
                                     qchigh, bleaf, curView, V, b, bp, bpp, 
                                     nextEventFlag, nextEventLOCK, qc, mvote, 
                                     mprop, mnew, VEntry, bpropose, c, qch, 
                                     debug, tmp, vb, key, val, node, bstar >>

nextevent(self) == /\ pc[self] = "nextevent"
                   /\ nextEventFlag[self] = TRUE /\ nextEventLOCK[self] = FALSE
                   /\ nextEventFlag' = [nextEventFlag EXCEPT ![self] = FALSE]
                   /\ /\ debug' = [debug EXCEPT ![self] = "loop"]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "PMOnBeat",
                                                               pc        |->  "loop",
                                                               tmp       |->  tmp[self],
                                                               debug     |->  debug[self] ] >>
                                                           \o stack[self]]
                   /\ tmp' = [tmp EXCEPT ![self] = defaultInitValue]
                   /\ pc' = [pc EXCEPT ![self] = "pmob1"]
                   /\ UNCHANGED << Ledger, sentValues, voteChannel, 
                                   newViewChannel, proposalChannel, 
                                   lastReadProposal, vheight, block, bexec, 
                                   qchigh, bleaf, curView, V, b, bp, bpp, 
                                   nextEventLOCK, qc, mvote, mprop, mnew, 
                                   VEntry, bpropose, c, qch, vb, key, val, 
                                   node, bstar >>

a(self) == p1(self) \/ p2(self) \/ loop(self) \/ p3(self)
              \/ receiveprop(self) \/ nextevent(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ OnPropose(self) \/ OnReceiveProposal(self)
                               \/ PMOnBeat(self) \/ MakeQC(self)
                               \/ AddItemToV(self) \/ OnReceiveVote(self)
                               \/ OnCommit(self) \/ Update(self))
           \/ (\E self \in ByzAcceptor: a(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat Mar 07 08:25:34 GMT 2020 by steve
\* Created Thu Feb 20 12:24:16 GMT 2020 by steve
