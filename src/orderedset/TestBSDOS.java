/*
 *  Copyright LIPN
 *  contributor(s) : Marc Champesme (2006) marc.champesme@lipn.univ-paris13.fr
 *  
 *  This software is a computer program whose purpose is the Incremental construction of Alpha lattices.
 *  
 *  This software is governed by the CeCILL license under French law and
 *  abiding by the rules of distribution of free software.  You can  use, 
 *  modify and/ or redistribute the software under the terms of the CeCILL
 *  license as circulated by CEA, CNRS and INRIA at the following URL
 *  "http://www.cecill.info". 
 *  
 *  As a counterpart to the access to the source code and  rights to copy,
 *  modify and redistribute granted by the license, users are provided only
 *  with a limited warranty  and the software's author,  the holder of the
 *  economic rights,  and the successive licensors  have only  limited
 *  liability. 
 *  
 *  In this respect, the user's attention is drawn to the risks associated
 *  with loading,  using,  modifying and/or developing or reproducing the
 *  software by the user in light of its specific status of free software,
 *  that may mean  that it is complicated to manipulate,  and  that  also
 *  therefore means  that it is reserved for developers  and  experienced
 *  professionals having in-depth computer knowledge. Users are therefore
 *  encouraged to load and test the software's suitability as regards their
 *  requirements in conditions enabling the security of their systems and/or 
 *  data to be ensured and,  more generally, to use and operate it in the 
 *  same conditions as regards security. 
 *  
 *  The fact that you are presently reading this means that you have had
 *  knowledge of the CeCILL license and that you accept its terms.
 */
package orderedset;

import java.util.Collection;
import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Set;
import java.util.SortedSet;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.TreeSet;
import java.util.Iterator;

/**
 *  Description of the Class
 *
 * @author     marc
 * @since      2 janvier 2006
 * @version    2 janvier 2006
 */
public class TestBSDOS {
	private List<String> objects;
	private List<String[]> arrayObjects;
	private List<List<String>> listObjects;
	private List<Set<String>> setObjects;
	private List<SortedSet<String>> sortedSetObjects;
	private List<OrderedSet<String>> orderedSetObjects;
	private List<BitSetDomainOrderedSet<String>> BSDorderedSetObjects;
	private List<Collection<String>> collectionObjects;


	/**
	 *  The main program for the TestBSDOS class
	 *
	 * @param  args  The command line arguments
	 */
	public static void main(String[] args) {
        String[] tabDomain = {"fghi", "ijk", "bcd", "hijk", "gh", "cdbe", "abc", "zzz", "jkl", "efg"};
        String[] tabContent = {"fghi", "ijk", "bcd", "hijk", "jkl"};
        String[] otherTab = {"bcd", "cdbe", "efg", "fghi", "gh", "hijk", "ijk", "jkl", "abc", "zzz"};
        ArrayHashSet<String> domain = new ArrayHashSet<String>(Arrays.asList(tabDomain));
		BitSetDomainOrderedSet<String> bsSet = new BitSetDomainOrderedSet<String>(domain);
        bsSet.addAll(Arrays.asList(tabContent));
        Set<String> otherSet = new HashSet<String>(Arrays.asList(otherTab));
        Set<String> resSet = bsSet.union(otherSet);
        System.out.println(bsSet + "\nunion " + otherSet + "\n=" + resSet);
		TestBSDOS test = new TestBSDOS();
		//test.testAdd();
		//test.testUnion();
        //test.testIntersection();
        test.testFastIntersection();
        test.testFastUnion();
        test.testContainsAll();
	}


	// -- main()

	/**
	 *  Constructor for the TestBSDOS object
	 */
	public TestBSDOS() {
		arrayObjects = makeArrayObjects();
		listObjects = makeListObjects();
		setObjects = makeSetObjects();
		sortedSetObjects = makeSortedSetObjects();
		orderedSetObjects = makeOrderedSetObjects();
		BSDorderedSetObjects = makeBSDOrderedSetObjects();
		collectionObjects = makeCollectionObjects();
		objects = makeObjects();
	}


	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<String[]> makeArrayObjects() {
        String[] tab1 = {"abzc", "bcd", "a","b", "cde", "egfg", "fghi", "geh",
				"hijk", "ijk", "jkl"};
        String[] tab2 = {"bcd", "cdbe", "efg", "fghi", "gh",
				"hijk", "ijk", "jkl", "abc", "zzz"};
        String[] tab3 = {"bcad", "cade", "cede", "efg", "fghi", "gh",
				"hijk", "ijk", "jkl", "abc", "zzz", "efg", "fghi", "gh"};
        String[] tab4 = {"cde", "czde", "efg", "fghi", "gh",
                        "hijk", "ijk", "jkel", "abc", "zzz", "efg", "fghi", "gh", "azp", "ppzza"};
        String[] tab5 = {"a","b", "yu", "cd", "cdt", "efe", "fgi", "ghv",
                        "hijk", "ijk", "jkl", "abc", "zzz", "efg", "fghi", "gh", "azp", "ppzza"};
		List<String[]> theList = new ArrayList<String[]>();
		theList.add(tab1);
		theList.add(tab2);
		theList.add(tab3);
        theList.add(tab4);
        theList.add(tab5);
		return theList;
	}


	// -- makeArrayObjects()

	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<Collection<String>> makeCollectionObjects() {
		List<Collection<String>> theList = new ArrayList<Collection<String>>();
		if (listObjects != null) {
			theList.addAll(listObjects);
		}
		if (setObjects != null) {
			theList.addAll(setObjects);
		}

		return theList;
	}


	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<List<String>> makeListObjects() {
		List<List<String>> theList = new ArrayList<List<String>>();
		if (arrayObjects == null) {
			arrayObjects = makeArrayObjects();
		}
		Iterator<String[]> iter = arrayObjects.iterator();
		while (iter.hasNext()) {
			theList.add(Arrays.asList(((String[]) iter.next())));
		}
		return theList;
	}


	// -- makeListObjects()

	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<Set<String>> makeSetObjects() {
		List<Set<String>> theList = new ArrayList<Set<String>>();
		if (listObjects == null) {
			listObjects = makeListObjects();
		}
		Iterator<List<String>> iter = listObjects.iterator();
		while (iter.hasNext()) {
			theList.add(new HashSet<String>((List<String>) iter.next()));
		}
		iter = listObjects.iterator();
		while (iter.hasNext()) {
			theList.add(new LinkedHashSet<String>((List<String>) iter.next()));
		}
		if (sortedSetObjects == null) {
			sortedSetObjects = makeSortedSetObjects();
		}
		theList.addAll(sortedSetObjects);

		return theList;
	}


	// -- makeSetObjects()

	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<SortedSet<String>> makeSortedSetObjects() {
		List<SortedSet<String>> theList = new ArrayList<SortedSet<String>>();
		if (listObjects == null) {
			listObjects = makeListObjects();
		}
		Iterator<List<String>> iter = listObjects.iterator();
		while (iter.hasNext()) {
			theList.add(new TreeSet<String>((List<String>) iter.next()));
		}

		return theList;
	}


	// -- makeSortedSetObjects()

	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<OrderedSet<String>> makeOrderedSetObjects() {
		List<OrderedSet<String>> theList = new ArrayList<OrderedSet<String>>();
		if (listObjects != null) {
			Iterator<List<String>> iter = listObjects.iterator();
			while (iter.hasNext()) {
				theList.add(new ArrayHashSet<String>((List<String>) iter.next()));
			}

		}
		if (setObjects != null) {
			Iterator<Set<String>> iter = setObjects.iterator();
			while (iter.hasNext()) {
				theList.add(new ArrayHashSet<String>((Set<String>) iter.next()));
			}

		}

		return theList;
	}


	// -- makeOrderedSetObjects()

	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<BitSetDomainOrderedSet<String>> makeBSDOrderedSetObjects() {
		System.out.print("Making BSDOrderedSet Objects:");
		List<BitSetDomainOrderedSet<String>> theList = new ArrayList<BitSetDomainOrderedSet<String>>();
        Set<String> domain = null;
		if (setObjects != null) {
            for (Set<String> aSet : setObjects) {
				BitSetDomainOrderedSet<String> bsdoSet;
				if (aSet instanceof SortedSet) {
					System.out.println("Set is a SortedSet:" + aSet);
					System.out.println("Skipping...");
					continue;
				}
				if (aSet.contains(null)) {
					System.out.println("Set contains null:" + aSet);
				}
                if (domain == null) {
                    domain = new ArrayHashSet<String>(aSet);
                } else {
                    aSet.retainAll(domain);
                }
				bsdoSet = new BitSetDomainOrderedSet<String>(domain);               
				bsdoSet.addAll(aSet);
				//@ set bsdoSet.elementType = \type(java.lang.Object);
				theList.add(bsdoSet);
				System.out.print(".");
			}

		}
		if (orderedSetObjects != null) {
			BitSetDomainOrderedSet<String> prevSet = null;
            for (OrderedSet<String> aSet : orderedSetObjects) {
				BitSetDomainOrderedSet<String> bsdoSet;
				if (aSet.contains(null)) {
					System.out.println("Set contains null");
				}
				bsdoSet = new BitSetDomainOrderedSet<String>(aSet);
				bsdoSet.addAll(bsdoSet.domain());
				if (prevSet != null) {
					bsdoSet.removeAll(prevSet);
				}
				//@ set bsdoSet.elementType = \type(java.lang.Object);
				theList.add(bsdoSet);
				System.out.print(".");
				prevSet = bsdoSet;
			}

		}
		System.out.println("done");
		return theList;
	}


	/**
	 *  Description of the Method
	 *
	 * @return    Description of the Return Value
	 */
	public List<String> makeObjects() {
		List<String> theList = new ArrayList<String>();
		theList.add("abc");
		theList.add("cde");
		theList.add("abcfg");
		theList.add("fgh");
		theList.add("zab");
		theList.add("qabc");
		theList.add("qcde");
		theList.add("qabcfg");
		theList.add("qfgh");
        theList.add("abzc");
        theList.add("qzab");
        theList.add("bcd");
        theList.add("a");
        theList.add("b");
        theList.add("cdbe");
        theList.add("fghi");
		//theList.addAll(collectionObjects);
		//theList.addAll(BSDorderedSetObjects);

		return theList;
	}

	// -- makeBSDOrderedSetObjects()

	/**
	 *  A unit test for JUnit
	 */
	public void testAdd() {
		System.out.println("\nTest add():");
		System.out.println("#objects:" + objects.size());
		System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
		Iterator<BitSetDomainOrderedSet<String>> iterSet = BSDorderedSetObjects.iterator();
		while (iterSet.hasNext()) {
			BitSetDomainOrderedSet<String> set = (BitSetDomainOrderedSet<String>) iterSet.next();
			System.out.print("\nAdding to set:" + set);
			Iterator<String> objIter = objects.iterator();
			while (objIter.hasNext()) {
				String o = objIter.next();
				//@ set set.elementType = \type(java.lang.Object);
				if (set.isAcceptableElement(o)) {
                    System.out.print("+" + o);
					set.add(o);
				} else {
                    System.out.print(".");            
                }
			}
		}
		System.out.println("\nTest add() done.");
	}
    
    public void testUnion() {
        List<BitSetDomainOrderedSet<String>> newSetObjects = new LinkedList<BitSetDomainOrderedSet<String>>();
        System.out.println("\nTest union():");
        System.out.println("#collections:" + collectionObjects.size());
        System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
        for (BitSetDomainOrderedSet<String> set : BSDorderedSetObjects) {
             System.out.println("\nUnion to set:" + set);
             for (Collection<String> c : collectionObjects) {
                //@ set set.elementType = \type(java.lang.Object);
                if (set.domain().containsAll(c)) {
                    System.out.print("+" + c);
                    newSetObjects.add(set.union(c));
                } else {
                    System.out.print(".");
                }
            }
        }
        System.out.println("\nAdding #BSDOSet to BSDOSet:" + newSetObjects.size());
        BSDorderedSetObjects.addAll(newSetObjects);
        System.out.println("Test union() done.");
       
    }

    public void testFastUnion() {
        List<BitSetDomainOrderedSet<String>> newSetObjects = new LinkedList<BitSetDomainOrderedSet<String>>();
        System.out.println("\n\n\nTest fastUnion():");
        System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
        for (BitSetDomainOrderedSet<String> set : BSDorderedSetObjects) {
            System.out.println("\n\nFastUnion to set:" + set);
            for (BitSetDomainOrderedSet<String> c : BSDorderedSetObjects) {
                //@ set set.elementType = \type(java.lang.Object);
                if (set.domain().containsAll(c)) {
                    System.out.print("+" + c);
                    newSetObjects.add(set.union(c));
                } else {
                    System.out.print(".");
                }
            }
        }
        System.out.println("\nAdding #BSDOSet to BSDOSet:" + newSetObjects.size());
        BSDorderedSetObjects.addAll(newSetObjects);
        System.out.println("Test fastUnion() done.");
       
    }

    public void testIntersection() {
        List<BitSetDomainOrderedSet<String>> newSetObjects = new LinkedList<BitSetDomainOrderedSet<String>>();
        System.out.println("\nTest intersection():");
        System.out.println("#collections:" + collectionObjects.size());
        System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
        for (BitSetDomainOrderedSet<String> set : BSDorderedSetObjects) {
             System.out.println("\nIntersection to set:" + set);
             for (Collection<String> c : collectionObjects) {
                //@ set set.elementType = \type(java.lang.Object);
                System.out.print("+" + c);
                newSetObjects.add(set.intersection(c));
            }
        }
        System.out.print("\nAdding #BSDOSet to BSDOSet:" + newSetObjects.size());
        BSDorderedSetObjects.addAll(newSetObjects);
        System.out.println("\nTest intersection() done.");
       
    }
    public void testFastIntersection() {
        List<BitSetDomainOrderedSet<String>> newSetObjects = new LinkedList<BitSetDomainOrderedSet<String>>();
        System.out.println("\n\n\nTest fastIntersection():");
        System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
        for (BitSetDomainOrderedSet<String> set : BSDorderedSetObjects) {
             System.out.println("\n\nFastIntersection to set:" + set);
             for (BitSetDomainOrderedSet<String> c : BSDorderedSetObjects) {
                //@ set set.elementType = \type(java.lang.Object);
                System.out.print("+" + c);
                newSetObjects.add(set.intersection(c));
            }
        }
        System.out.print("\nAdding #BSDOSet to BSDOSet:" + newSetObjects.size());
        BSDorderedSetObjects.addAll(newSetObjects);
        System.out.println("\nTest fastIntersection() done.");
       
    }
    public void testContainsAll() {
        System.out.println("\n\n\nTest containsAll():");
        System.out.println("#BSDOSet:" + BSDorderedSetObjects.size());
        for (BitSetDomainOrderedSet<String> set : BSDorderedSetObjects) {
            System.out.print("\n\nDoes "+ set);
            for (BitSetDomainOrderedSet<String> c : BSDorderedSetObjects) {
                //@ set set.elementType = \type(java.lang.Object);
                System.out.println("\ncontainsAll(" + c + ")->" + set.containsAll(c));
            }
        }
        System.out.println("\nTest containsAll() done.");
       
    }
}
// -- end class TestBSDOS.java

