module treeset

open Integer5

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
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11 = ff2.univ + bf2.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11 = ff3.univ + bf3.univ   

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


fun FReach[] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
    (QF.thiz_0).(QF.root_0).*(QF.fleft_0 + QF.fright_0) - null
}


one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11 extends TreeSetIntVarNode {}


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



fact { QF.fleft_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->null+N8->N9+N8->N10+N8->N11+N8->null+N9->N10+N9->N11+N9->null+N10->N11+N10->null+N11->null }
fact { QF.fright_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->null+N8->N9+N8->N10+N8->N11+N8->null+N9->N10+N9->N11+N9->null+N10->N11+N10->null+N11->null }
fact { QF.fparent_0 in N0->N1+N0->N2+N0->N3+N0->N4+N0->N5+N0->N6+N0->N7+N0->N8+N0->N9+N0->N10+N0->N11+N0->null+N1->N2+N1->N3+N1->N4+N1->N5+N1->N6+N1->N7+N1->N8+N1->N9+N1->N10+N1->N11+N1->null+N2->N3+N2->N4+N2->N5+N2->N6+N2->N7+N2->N8+N2->N9+N2->N10+N2->N11+N2->null+N3->N4+N3->N5+N3->N6+N3->N7+N3->N8+N3->N9+N3->N10+N3->N11+N3->null+N4->N5+N4->N6+N4->N7+N4->N8+N4->N9+N4->N10+N4->N11+N4->null+N5->N6+N5->N7+N5->N8+N5->N9+N5->N10+N5->N11+N5->null+N6->N7+N6->N8+N6->N9+N6->N10+N6->N11+N6->null+N7->N8+N7->N9+N7->N10+N7->N11+N7->null+N8->N9+N8->N10+N8->N11+N8->null+N9->N10+N9->N11+N9->null+N10->N11+N10->null+N11->null }
fact { QF.bleft_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11 }
fact { QF.bright_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11 }
fact { QF.bparent_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2+N3->N0+N3->N1+N3->N2+N3->N3+N4->N0+N4->N1+N4->N2+N4->N3+N4->N4+N5->N0+N5->N1+N5->N2+N5->N3+N5->N4+N5->N5+N6->N0+N6->N1+N6->N2+N6->N3+N6->N4+N6->N5+N6->N6+N7->N0+N7->N1+N7->N2+N7->N3+N7->N4+N7->N5+N7->N6+N7->N7+N8->N0+N8->N1+N8->N2+N8->N3+N8->N4+N8->N5+N8->N6+N8->N7+N8->N8+N9->N0+N9->N1+N9->N2+N9->N3+N9->N4+N9->N5+N9->N6+N9->N7+N9->N8+N9->N9+N10->N0+N10->N1+N10->N2+N10->N3+N10->N4+N10->N5+N10->N6+N10->N7+N10->N8+N10->N9+N10->N10+N11->N0+N11->N1+N11->N2+N11->N3+N11->N4+N11->N5+N11->N6+N11->N7+N11->N8+N11->N9+N11->N10+N11->N11 }


fact {
	(QF.key_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->null
}


fact {
	(QF.size_0) in TreeSetIntVar->i320+TreeSetIntVar->i321+TreeSetIntVar->i322+TreeSetIntVar->i323+TreeSetIntVar->i324+TreeSetIntVar->i325+TreeSetIntVar->i326+TreeSetIntVar->i327+TreeSetIntVar->i328+TreeSetIntVar->i329+TreeSetIntVar->i3210+TreeSetIntVar->i3211+TreeSetIntVar->i3212
}


fact {
	(QF.blackHeight_0) in N0->i320+N0->i321+N0->i322+N0->i323+N0->i324+N0->i325+N0->i326+N0->i327+N0->i328+N0->i329+N0->i3210+N0->i3211+N0->null+N1->i320+N1->i321+N1->i322+N1->i323+N1->i324+N1->i325+N1->i326+N1->i327+N1->i328+N1->i329+N1->i3210+N1->i3211+N1->null+N2->i320+N2->i321+N2->i322+N2->i323+N2->i324+N2->i325+N2->i326+N2->i327+N2->i328+N2->i329+N2->i3210+N2->i3211+N2->null+N3->i320+N3->i321+N3->i322+N3->i323+N3->i324+N3->i325+N3->i326+N3->i327+N3->i328+N3->i329+N3->i3210+N3->i3211+N3->null+N4->i320+N4->i321+N4->i322+N4->i323+N4->i324+N4->i325+N4->i326+N4->i327+N4->i328+N4->i329+N4->i3210+N4->i3211+N4->null+N5->i320+N5->i321+N5->i322+N5->i323+N5->i324+N5->i325+N5->i326+N5->i327+N5->i328+N5->i329+N5->i3210+N5->i3211+N5->null+N6->i320+N6->i321+N6->i322+N6->i323+N6->i324+N6->i325+N6->i326+N6->i327+N6->i328+N6->i329+N6->i3210+N6->i3211+N6->null+N7->i320+N7->i321+N7->i322+N7->i323+N7->i324+N7->i325+N7->i326+N7->i327+N7->i328+N7->i329+N7->i3210+N7->i3211+N7->null+N8->i320+N8->i321+N8->i322+N8->i323+N8->i324+N8->i325+N8->i326+N8->i327+N8->i328+N8->i329+N8->i3210+N8->i3211+N8->null+N9->i320+N9->i321+N9->i322+N9->i323+N9->i324+N9->i325+N9->i326+N9->i327+N9->i328+N9->i329+N9->i3210+N9->i3211+N9->null+N10->i320+N10->i321+N10->i322+N10->i323+N10->i324+N10->i325+N10->i326+N10->i327+N10->i328+N10->i329+N10->i3210+N10->i3211+N10->null+N11->i320+N11->i321+N11->i322+N11->i323+N11->i324+N11->i325+N11->i326+N11->i327+N11->i328+N11->i329+N11->i3210+N11->i3211+N11->null
}




fun node_max[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
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
 )
}


fact {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323) or
	  (m = N3 and size = i324) or
	  (m = N4 and size = i325) or
	  (m = N5 and size = i326) or
	  (m = N6 and size = i327) or
	  (m = N7 and size = i328) or
	  (m = N8 and size = i329) or
	  (m = N9 and size = i3210) or
	  (m = N10 and size = i3211) or
	  (m = N11 and size = i3212)
}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 TreeSetIntVar, exactly 12 TreeSetIntVarNode, 1 int, exactly 13 JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
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
}


fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
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
 )
}


fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
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
 )
}


fun node_relprevs[] : (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) -> set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
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
}


fun node_min[es: set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)] : lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11) {
 es - es.(
   N0->(N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N1->(N2+N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N2->(N3+N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N3->(N4+N5+N6+N7+N8+N9+N10+N11)
   +
   N4->(N5+N6+N7+N8+N9+N10+N11)
   +
   N5->(N6+N7+N8+N9+N10+N11)
   +
   N6->(N7+N8+N9+N10+N11)
   +
   N7->(N8+N9+N10+N11)
   +
   N8->(N9+N10+N11)
   +
   N9->(N10+N11)
   +
   N10->(N11)
 )
}




