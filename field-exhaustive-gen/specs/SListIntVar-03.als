module slistintvar

open Integer3

one sig null {}

one sig SListIntVar  {}

abstract sig SListIntVarNode {}


one sig QF {
  thiz_0:      one SListIntVar,
  head_0:      SListIntVar ->one(SListIntVarNode+null),
  nodeValue_0: SListIntVarNode ->one(JavaPrimitiveIntegerValue+null),
  //index_0: SListIntVarNode -> lone JavaPrimitiveIntegerValue,
  fnext_0:     SListIntVarNode ->lone(SListIntVarNode+null),
  bnext_0:     SListIntVarNode ->lone(SListIntVarNode+null),
  size_0:      SListIntVar ->one JavaPrimitiveIntegerValue,
}


fact repOk {
  let next = QF.fnext_0+QF.bnext_0,
      thiz = QF.thiz_0,
      head = QF.head_0,
      value = QF.nodeValue_0/*,
      index = QF.index_0*/ |
  {
    thiz.head != null
    thiz.head.value = i320
    // no cycles 
    all n: thiz.head.*next-null | { n !in n.next.*next and n.value != null }
    // compute indexes for nodes
    /*(thiz.head!=null => thiz.head.index = i320
                             and
                             (all n1,n2: thiz.head.*next-null | n1.next = n2 implies fun_java_primitive_integer_value_add[n1.index,i321] = n2.index)
    )*/
    // sorted
    all n: thiz.head.^next-null | { n.next != null implies pred_java_primitive_integer_value_lte[n.value, n.next.value] }
    
  }
}

fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
--    ( pred_java_primitive_integer_value_eq[a,b]) 

}


//fact orderingAxiom1 
fact { 
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fnext_0,bf1=QF.bnext_0 | { 
-- forwardPlusBackwardAreFunctions
no ((ff1.univ) & (bf1.univ)) 
N0+N1+N2 = ff1.univ + bf1.univ 
--forwardIsIndeedForward 
entry in N0+null 
all n : entry.*ff1 - null | node_min[ff1.n] in node_prevs[n] 
all disj n1, n2 : entry.*ff1 - null | 
{ 
      ( some (ff1.n1 ) && some (ff1.n2 ) && node_min[ff1.n1 ] in 
      node_prevs[node_min[ff1.n2 ]] ) 
        implies n1 in node_prevs[n2] 
  } 
  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs)
  --prefixReachableForward 
    all x : entry.*(ff1) -null | node_prevs[x] in entry.*(ff1) 
} 
} 



fact fixReachable {all n : SListIntVarNode | n !in (QF.thiz_0).(QF.head_0).*(QF.fnext_0) implies
		(
			n.(QF.nodeValue_0) = i320 and
            //no n.(QF.index_0) and
			n.(QF.fnext_0) = null and
			no n.(QF.bnext_0)
		)
}


fun FReach[] :set (N0+N1+N2) {
    (QF.thiz_0).(QF.head_0).*(QF.fnext_0)-null
}

one sig N0,N1,N2 extends SListIntVarNode {}


one sig i320,i321,i322 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true
	i320->false+i321->false+i322->true in b01
	b00 in i320->false+i321->true+i322->false
	i320->false+i321->true+i322->false in b00
	b02 in i320->false+i321->false+i322->false
	i320->false+i321->false+i322->false in b02
}



fact { QF.fnext_0 in N0->N1+N0->N2+N0->null+N1->N2+N1->null+N2->null }
fact { QF.bnext_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2 }


fact {
	(QF.nodeValue_0) in N0->i320+N0->i321+N0->null+N1->i320+N1->i321+N1->null+N2->i320+N2->i321+N2->null
}


fact {
	(QF.size_0) in SListIntVar->i320+SListIntVar->i321+SListIntVar->i322
}




// myseq definitions
fun int32_max[es: set (i320+i321+i322)] : lone (i320+i321+i322) {
 es - es.(
   i321->(i320)
   +
   i322->(i320+i321)
 )
}


fun int32_prevs[e: i320+i321+i322] :set (i320+i321+i322) {
 e.(
   i321->(i320)
   +
   i322->(i320+i321)
 )
}


pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {
	let dom = s.JavaPrimitiveIntegerValue |
		(no dom and res = i320) or 
		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])
}


// end of myseq definitions


fun node_max[es: set (N0+N1+N2)] : lone (N0+N1+N2) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (m = N0 and size = i320) or
	  (m = N1 and size = i321) or
	  (m = N2 and size = i322)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 SListIntVar, exactly 3 SListIntVarNode, 1 int, exactly 3 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2) -> lone (N0+N1+N2) {
 N0->N1
 +
 N1->N2
}


fun node_prevs[e: N0+N1+N2] :set (N0+N1+N2) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
 )
}


fun node_rprevs[e: N0+N1+N2] :set (N0+N1+N2) {
 e.(
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
 )
}


fun node_relprevs[] : (N0+N1+N2) -> set (N0+N1+N2) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
}


fun node_min[es: set (N0+N1+N2)] : lone (N0+N1+N2) {
 es - es.(
   N0->(N1+N2)
   +
   N1->(N2)
 )
}




