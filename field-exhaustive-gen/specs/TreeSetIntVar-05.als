module treeset

open Integer4

one sig null {}


one sig TreeSetIntVar {}

abstract sig TreeSetIntVarNode  {}

one sig QF {
    thiz_0:        one TreeSetIntVar, 
    root_0:        TreeSetIntVar -> one (TreeSetIntVarNode+null),
    key_0:         TreeSetIntVarNode -> one (JavaPrimitiveIntegerValue+null),
    blackHeight_0: TreeSetIntVarNode -> one JavaPrimitiveIntegerValue,
    color_0:       TreeSetIntVarNode -> one (boolean),
    fparent_0:      TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bparent_0:      TreeSetIntVarNode -> lone (TreeSetIntVarNode),

    fleft_0:        TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bleft_0:        TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    fright_0:       TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    bright_0:       TreeSetIntVarNode -> lone (TreeSetIntVarNode+null),
    size_0:        TreeSetIntVar -> one JavaPrimitiveIntegerValue    

}


fact repOk {
   let RED = false,
       BLACK = true,
       key = QF.key_0,
       blackHeight = QF.blackHeight_0,
       left = QF.fleft_0 +QF.bleft_0,
       right = QF.fright_0+QF.bright_0,
       color = QF.color_0,
       parent = QF.fparent_0 + QF.bparent_0,
       root = QF.root_0,
       thiz = QF.thiz_0
   | {

		RED=false &&
		BLACK=true && 
		
        thiz.root.parent in null && 
//		( thiz.root!=null => thiz.root.color = BLACK ) && 
		( all n: TreeSetIntVarNode | n in thiz.root.*(left + right) => (

				/*non_null*/
                                (n.key != null ) &&

				/* parent left */
                                ( n.left != null => n.left.parent = n ) &&

				/* parent right */
				( n.right != null => n.right.parent = n ) &&

				/* parent */
				( n.parent != null => n in n.parent.(left + right) ) &&

				/* form a tree */
				( n !in n.^parent ) &&

				/* left sorted */
				( all x : n.left.^(left + right) + n.left - null | pred_java_primitive_integer_value_gt[n.key,x.key]) &&

				/* right sorted */
				( all x : n.right.^(left + right) + n.right - null | pred_java_primitive_integer_value_gt[x.key,n.key]) &&

				/* no red node has a red parent */
				( n.color = RED && n.parent != null => n.parent.color = BLACK ) &&

				/* black height leaf */
				( ( n.left=null && n.right=null ) => ( equ[n.blackHeight,i321] ) ) &&

				/* black height left non null */
				( n.left!=null && n.right=null => ( 
				      ( n.left.color = RED ) && 
				      ( equ[n.left.blackHeight,i321] ) && 
				      ( equ[n.blackHeight,i321] )  
				)) &&

				/* black height right non null */
				( n.left=null && n.right!=null =>  ( 
				      ( n.right.color = RED ) && 
				      ( equ[n.right.blackHeight,i321] ) && 
				      ( equ[n.blackHeight,i321] ) 
				 )) && 

				/* inner node (RED/RED) */
				( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=RED => ( 
				        ( equ[n.left.blackHeight,n.right.blackHeight] ) && 
				        ( equ[n.blackHeight, n.left.blackHeight] ) 
				)) && 

				/* inner node (BLACK/BLACK) */
				( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=BLACK => ( 
				        ( equ[n.left.blackHeight,n.right.blackHeight] ) && 
				        ( equ[n.blackHeight,fun_java_primitive_integer_value_add[n.left.blackHeight,i321]] )  
				)) && 

				/* inner node (RED/BLACK) */
				( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=BLACK => ( 
				        ( equ[n.left.blackHeight,fun_java_primitive_integer_value_add[n.right.blackHeight,i321]] ) && 
				        ( equ[n.blackHeight,n.left.blackHeight]  )  
				)) && 

				/* inner node (BLACK/RED) */
				( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=RED => ( 
				        ( equ[n.right.blackHeight,fun_java_primitive_integer_value_add[n.left.blackHeight,i321]] ) && 
				        ( equ[n.blackHeight,n.right.blackHeight]  )   )) 

			)	)

}}



fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
}


fact { 
let entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,ff3=QF.fparent_0,bf1=QF.bleft_0,bf2=QF.bright_0,bf3=QF.bparent_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   no ((ff3.univ) & (bf3.univ)) 
   N0+N1+N2+N3+N4 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4 = ff2.univ + bf2.univ   
   N0+N1+N2+N3+N4 = ff3.univ + bf3.univ   

  --forwardIsIndeedForward 
  entry in N0+null and 
  (all n : entry.*(ff1 + ff2) - null | ( 
   node_min[(ff1).n] in node_prevs[n]) and ( 
    node_min[(ff2).n] in node_prevs[n])) and 
  (all disj n1, n2 : entry.*((ff1) + (ff2)) - null | ( 
        (    some ((ff1).n1 + (ff2).n1) and 
            some ((ff1).n2 + (ff2).n2) and 
                node_min[(ff1).n1 + (ff2).n1] in node_prevs[node_min[(ff1).n2 + (ff2).n2]] 
             ) implies n1 in node_prevs[n2] 
   ) 
   and 
     let a = node_min[(ff1).n1 + (ff2).n1] | 
     let b = node_min[(ff1).n2 + (ff2).n2] | 
     (some ((ff1).n1 + (ff2).n1) and a = b and a.(ff1) = n1 and a.(ff2) = n2) implies n2 = n1.node_next[] 
   ) 

  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs) && (bf2 in node_relprevs) 

  --prefixReachableForward 
    all x : entry.*(ff1 +ff2) -null | node_prevs[x] in entry.*(ff1 + ff2) 

} 
} 



fact notReachableIsFix {all n : TreeSetIntVarNode | n in (TreeSetIntVarNode - (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0 + QF.fparent_0)) => (
                        no n.(QF.bleft_0) and
                        no n.(QF.bright_0) and
                        no n.(QF.bparent_0) and
                        n.(QF.fleft_0) = null and
                        n.(QF.fright_0) = null and
                        n.(QF.fparent_0) = null and
                        n.(QF.color_0) = false  and
                        n.(QF.blackHeight_0) = i320 and
                        n.(QF.key_0) = i320 
        )
}


fun FReach[] :set (N0+N1+N2+N3+N4) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}


one sig N0,N1,N2,N3,N4 extends TreeSetIntVarNode {}


one sig i320,i321,i322,i323,i324,i325 extends JavaPrimitiveIntegerValue {} 
fact {
	// int32 bounds 
	b01 in i320->false+i321->false+i322->true+i323->true+i324->false+i325->false
	i320->false+i321->false+i322->true+i323->true+i324->false+i325->false in b01
	b00 in i320->false+i321->true+i322->false+i323->true+i324->false+i325->true
	i320->false+i321->true+i322->false+i323->true+i324->false+i325->true in b00
	b03 in i320->false+i321->false+i322->false+i323->false+i324->false+i325->false
	i320->false+i321->false+i322->false+i323->false+i324->false+i325->false in b03
	b02 in i320->false+i321->false+i322->false+i323->false+i324->true+i325->true
	i320->false+i321->false+i322->false+i323->false+i324->true+i325->true in b02
}



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->null+N1->N2+N1->N3+N1->N4+N1->null+N2->N3+N2->N4+N2->null+N3->N4+N3->null+N4->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->null
}


fact {
	(QF.size_0) in TreeSetIntVar->i320+TreeSetIntVar->i321+TreeSetIntVar->i322+TreeSetIntVar->i323+TreeSetIntVar->i324+TreeSetIntVar->i325
}


fact {
	(QF.blackHeight_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->null
}




fun node_max[es: set (N0+N1+N2+N3+N4)] : lone (N0+N1+N2+N3+N4) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323) or
	  (m = N3 and size = i324) or
	  (m = N4 and size = i325)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 TreeSetIntVar, exactly 5 TreeSetIntVarNode, 1 int, exactly 6 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4) -> lone (N0+N1+N2+N3+N4) {
 N0->N1
 +
 N1->N2
 +
 N2->N3
 +
 N3->N4
}


fun node_prevs[e: N0+N1+N2+N3+N4] :set (N0+N1+N2+N3+N4) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
   +
   N3->(N0+N1+N2)
   +
   N4->(N0+N1+N2+N3)
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4] :set (N0+N1+N2+N3+N4) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4) -> set (N0+N1+N2+N3+N4) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
   +
   N3->(N0+N1+N2+N3)
   +
   N4->(N0+N1+N2+N3+N4)
}


fun node_min[es: set (N0+N1+N2+N3+N4)] : lone (N0+N1+N2+N3+N4) {
 es - es.(
   N0->(N1+N2+N3+N4)
   +
   N1->(N2+N3+N4)
   +
   N2->(N3+N4)
   +
   N3->(N4)
 )
}




