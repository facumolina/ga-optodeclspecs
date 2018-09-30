module slistintvar

open Integer5

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
N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12 = ff1.univ + bf1.univ 
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


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
    (QF.thiz_0).(QF.head_0).*(QF.fnext_0)-null
}

one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12 extends SListIntVarNode {}


one sig i320,i321,i322,i323,i324,i325,i326,i327,i328,i329,i3210,i3211,i3212 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false+i326->true+i327->true+i328->false+i329->false+i3210->true+i3211->true+i3212->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true+i326->false+i327->true+i328->false+i329->true+i3210->false+i3211->true+i3212->false in b00
	b04 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->false+i329->false+i3210->false+i3211->false+i3212->false in b04
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false+i326->false+i327->false+i328->true+i329->true+i3210->true+i3211->true+i3212->true in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true+i326->true+i327->true+i328->false+i329->false+i3210->false+i3211->false+i3212->true in b02
}



fact { QF.fnext_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->N12+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->N12+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->N12+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->N12+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->N12+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->N12+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->N12+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->N12+N7->null+N8->N9+N8->N10+N8->N11+N8->N12+N8->null+N9->N10+N9->N11+N9->N12+N9->null+N10->N11+N10->N12+N10->null+N11->N12+N11->null+N12->null }
fact { QF.bnext_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11+N12->N0+N12->N1+N12->N2+N12->N3+N12->N4+N12->N5+N12->N6+N12->N7+N12->N8+N12->N9+N12->N10+N12->N11+N12->N12 }


fact {
	(QF.nodeValue_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->null+N12->i320+N12->i321+N12->i322+N12->i323+N12->i324+N12->i325+N12->i326+N12->i327+N12->i328+N12->i329+N12->i3210+N12->i3211+N12->null
}


fact {
	(QF.size_0) in SListIntVar->i320+SListIntVar->i321+SListIntVar->i322+SListIntVar->i323+SListIntVar->i324+SListIntVar->i325+SListIntVar->i326+SListIntVar->i327+SListIntVar->i328+SListIntVar->i329+SListIntVar->i3210+SListIntVar->i3211+SListIntVar->i3212
}




// myseq definitions
fun int32_max[es: set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212)] : lone (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212) {
 es - es.(
   i321->(i320)
   +
   i322->(i320+i321)
   +
   i323->(i320+i321+i322)
   +
   i324->(i320+i321+i322+i323)
   +
   i325->(i320+i321+i322+i323+i324)
   +
   i326->(i320+i321+i322+i323+i324+i325)
   +
   i327->(i320+i321+i322+i323+i324+i325+i326)
   +
   i328->(i320+i321+i322+i323+i324+i325+i326+i327)
   +
   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)
   +
   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)
   +
   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)
   +
   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)
 )
}


fun int32_prevs[e: i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212] :set (i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211+i3212) {
 e.(
   i321->(i320)
   +
   i322->(i320+i321)
   +
   i323->(i320+i321+i322)
   +
   i324->(i320+i321+i322+i323)
   +
   i325->(i320+i321+i322+i323+i324)
   +
   i326->(i320+i321+i322+i323+i324+i325)
   +
   i327->(i320+i321+i322+i323+i324+i325+i326)
   +
   i328->(i320+i321+i322+i323+i324+i325+i326+i327)
   +
   i329->(i320+i321+i322+i323+i324+i325+i326+i327+i328)
   +
   i3210->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329)
   +
   i3211->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210)
   +
   i3212->(i320+i321+i322+i323+i324+i325+i326+i327+i328+i329+i3210+i3211)
 )
}


pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {
	let dom = s.JavaPrimitiveIntegerValue |
		(no dom and res = i320) or 
		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])
}


// end of myseq definitions


fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (m = N0 and size = i320) or
	  (m = N1 and size = i321) or
	  (m = N2 and size = i322) or
	  (m = N3 and size = i323) or
	  (m = N4 and size = i324) or
	  (m = N5 and size = i325) or
	  (m = N6 and size = i326) or
	  (m = N7 and size = i327) or
	  (m = N8 and size = i328) or
	  (m = N9 and size = i329) or
	  (m = N10 and size = i3210) or
	  (m = N11 and size = i3211) or
	  (m = N12 and size = i3212)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 SListIntVar, exactly 13 SListIntVarNode, 1 int, exactly 13 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
 +
 N4->N5
 +
 N5->N6
 +
 N6->N7
 +
 N7->N8
 +
 N8->N9
 +
 N9->N10
 +
 N10->N11
 +
 N11->N12
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
   +
   N5->(N0+N1+N2+N3+N4)
   +
   N6->(N0+N1+N2+N3+N4+N5)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 e.(
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
   +
   N5->(N0+N1+N2+N3+N4+N5)
   +
   N6->(N0+N1+N2+N3+N4+N5+N6)
   +
   N7->(N0+N1+N2+N3+N4+N5+N6+N7)
   +
   N8->(N0+N1+N2+N3+N4+N5+N6+N7+N8)
   +
   N9->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9)
   +
   N10->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)
   +
   N11->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N12->(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11+N12)
   +
   N5->(N6+N7+N8+N9+N10+N11+N12)
   +
   N6->(N7+N8+N9+N10+N11+N12)
   +
   N7->(N8+N9+N10+N11+N12)
   +
   N8->(N9+N10+N11+N12)
   +
   N9->(N10+N11+N12)
   +
   N10->(N11+N12)
   +
   N11->(N12)
 )
}




