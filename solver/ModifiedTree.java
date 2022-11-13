package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.List;



/*
 *   To handle toplogical things
 * 
 */

public class ModifiedTree {
	
	Node head;
	
	static class Node{
		String regionName;
		List<Node> next; 
		
		// Constructor
		Node(String name){
			regionName = name;
			next = new ArrayList<>();
			
		}
		
		@Override
	     public String toString() {
			return "Node:- name:" + regionName + ", next:" + next; 
		}
		
	}
	
	ModifiedTree(String name){
		head = new Node(name);
	}
	
	  
     // Method to insert a new node
     public static ModifiedTree insert(ModifiedTree list,Node node, String name) {
        	
    	 
    	 Node newnode = new Node(name);
    	 node.next.add(newnode);
    	 
    	 return list;
    			 
     }
     
     
     @Override
     public String toString() {
    	 
    	 return head.toString();
    	 
     }
   
        
        
	
	
	
	
	
	
	
	
	
	
}
