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
package lattice.alpha.util;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import lattice.util.concept.DefaultFormalAttribute;
import lattice.util.concept.DefaultFormalObject;
import lattice.util.concept.FormalAttribute;
import lattice.util.concept.FormalObject;
import lattice.util.exception.BadInputDataException;
import lattice.util.relation.MatrixBinaryRelationBuilder;
import lattice.util.relation.RelationalContextFamily;

/**
 * Class AlphaContext
 */
public class AlphaContext implements Iterable<Couple<FormalObject, FormalAttribute>>{
    /*@
      @ public invariant getName() != null;
      @ public invariant objectNumber() >= 0;
      @ public invariant attributeNumber() >= 0;
      @ public invariant classNumber() >= 0;
      @ public invariant attributeNumber() >= classNumber();
      @*/
    // Fields
    private String name = "An Alpha Context";

    /** 
     * A mapping from object names (i.e. instances of String) to FormalObject with same names.
     * Keys are String instances and values are FormalObject instances.
     */
    private Map<String, FormalObject> nameToFObject;

    /**
     * A mapping from attribute names (i.e. instances of String) to 
     * FormalAttributes with same names. No distinction is made between standard attributes 
     * and class attributes (attributes which represent classes). Keys are String
     * instances and values are FormalAttribute instances. 
     */
    private Map<String, FormalAttribute> nameToFAttribute;

    /**
     * A mapping from FormalAttribute representing class attributes to
     * sets of objects, which represent these classes. The key set of this
     * map is the set of classes of this AlphaContext. Keys are FormalAttribute
     * instances and values are Set instances, whose elements are FormalObject
     * instances.
     */
    private Map<FormalAttribute, Set<FormalObject>> classAttrToObjectSet;

    /**
     * A mapping from FormalObject to the description (i.e. intent) of
     * these objects. Keys are FormalObject instances and values are Set
     * instances whose elements are FormalAttributes.
     */
    private Map<FormalObject, Set<FormalAttribute>> fObjectToIntent;

    /**
     * Initialize an empty context with a default name.
     */
    /*@
      @ ensures getName() != null;
      @ ensures attributeNumber() == 0;
      @ ensures objectNumber() == 0;
      @ ensures classNumber() == 0;
      @*/
    public AlphaContext() {
        nameToFObject = new HashMap<String, FormalObject>();
        nameToFAttribute = new HashMap<String, FormalAttribute>();
        classAttrToObjectSet = new HashMap<FormalAttribute, Set<FormalObject>>();
        fObjectToIntent = new HashMap<FormalObject, Set<FormalAttribute>>();

    }

    /**
     * Initialize an empty context with the specified name.
     * @param name the name of the new context
     */
    /*@
      @ requires name != null;
      @ ensures getName().equals(name);
      @ ensures attributeNumber() == 0;
      @ ensures objectNumber() == 0;
      @ ensures classNumber() == 0;
      @*/
    public AlphaContext(String name) {
        this();
        this.name = name;
    }

    public AlphaContext(String contextName, int expectedObjNumber, int expectedAttrNumber, int expectedClassNumber) {
        float loadFactor = 0.75f;
        int objCapacity = Math.round(expectedObjNumber / loadFactor);
        name = contextName;
        nameToFObject = new HashMap<String, FormalObject>(objCapacity);
        nameToFAttribute = new HashMap<String, FormalAttribute>(Math.round(expectedAttrNumber / loadFactor));
        classAttrToObjectSet = new HashMap<FormalAttribute, Set<FormalObject>>(Math.round(expectedClassNumber / loadFactor));
        fObjectToIntent = new HashMap<FormalObject, Set<FormalAttribute>>(objCapacity);
    }
    /**
     * Adds the specified attribute to the intent of the specified object if
     * it is not already present.
     * 
     * @param obj the object to which the specified attribute is to be added 
     * to the intent
     * @param attribute the attribute to add to the intent of the specified object
     * @return true if the intent of the specified object did not already contain 
     * the specified attribute ; false otherwise.
     */
    /*@
      @ requires obj != null;
      @ requires attribute != null;
      @ requires obj == getObjectForName(obj.getName());
      @ requires attribute == getAttributeForName(attribute.getName());
      @ ensures getIntentOfObject(obj).contains(attribute);
      @ ensures \result <==> !\old(getIntentOfObject(obj).contains(attribute));
      @*/
    public boolean addAttributeToObject(FormalObject obj, FormalAttribute attribute) {
        Set<FormalAttribute> intent = fObjectToIntent.get(obj);
        if (intent == null) {
            intent = new HashSet<FormalAttribute>();
            fObjectToIntent.put(obj, intent);
        }
        return intent.add(attribute);
    }
 
    /**
     * Adds a FormalObject with the specified name to this context if
     * it is not already present.
     * 
     * @param objectName the name of the FormalObject to add
     * @return true if this context did not already contain 
     * a FormalObject with the specified name ; false otherwise.
     */
    /*@
      @ requires objectName != null;
      @ ensures containsObjectForName(objectName);
      @ ensures \result ==> getIntentOfObject(getObjectForName(objectName)).isEmpty();
      @ ensures \result <==> !\old(containsObjectForName(objectName));
      @*/
    public boolean addObjectForName(String objectName) {
        FormalObject obj = nameToFObject.get(objectName);
        if (obj == null) {
            obj = new DefaultFormalObject(objectName);
            nameToFObject.put(objectName, obj);
            fObjectToIntent.put(obj, new HashSet<FormalAttribute>());
            return true;
        }
        //@ assume fObjectToIntent.containsKey(obj);
        return false;
   }

    /**
     * @param relation
     * @param obj
     * @return void
     */
    public boolean addObjectToClass(FormalAttribute classAttr, FormalObject obj) {
        Set<FormalObject> objectSet = classAttrToObjectSet.get(classAttr);
        return objectSet.add(obj);
    }

    /**
     * @param objectName
     * @param className
     * @param attributeName
     * @return
     */
    public boolean addTriplet(String objectName, String className, String attributeName) {
        int modCount = 0; 
        FormalObject object = nameToFObject.get(objectName);
        FormalAttribute classAttr = nameToFAttribute.get(className);
        FormalAttribute attribute = nameToFAttribute.get(attributeName);
        Set<FormalAttribute> objIntent;
        Set<FormalObject> classObjectSet;
        if (object == null) {
            object = new DefaultFormalObject(objectName);
            nameToFObject.put(objectName, object);
            objIntent = new HashSet<FormalAttribute>();
            fObjectToIntent.put(object, objIntent);
            modCount += 2;
        } else {
            objIntent = fObjectToIntent.get(object);
            //@ assume !objIntent.isEmpty();
        }
        //@ assume object != null;
        //@ assume objIntent != null;

        if (classAttr == null) {
            classAttr = new DefaultFormalAttribute(className);
            nameToFAttribute.put(className, classAttr);
            classObjectSet = new HashSet<FormalObject>();
            classAttrToObjectSet.put(classAttr, classObjectSet);
            modCount += 2;
        } else {
            classObjectSet = classAttrToObjectSet.get(classAttr);
            //@ assume !classObjectSet.isEmpty();
        }
        //@ assume classAttr != null;
        //@ assume classObjectSet instanceof Set;
        if (classObjectSet.add(object)) {
            modCount++;
        }
        if (objIntent.add(classAttr)) {
            modCount++;
        }

        if (attribute == null) {
            attribute = new DefaultFormalAttribute(attributeName);
            nameToFAttribute.put(attributeName, attribute);
            modCount++;
        }
        
        if (objIntent.add(attribute)) {
            modCount++;
        }
        
        return modCount != 0;
    }
    
    public RelationalContextFamily asRelationalContextFamily() {
        RelationalContextFamily relCtx = new RelationalContextFamily();
        Iterator<FormalAttribute> classIter = getClasses().iterator();
        while (classIter.hasNext()) {
            FormalAttribute classAttr = classIter.next();
            relCtx.add(classToMatrixBinaryRelation(classAttr));
        }
        return relCtx;
    }
    
    /**
     * Returns the number of FormalAttribute currently present
     * in this context.
     * @return the number of FormalAttribute of this context.
     */
    /*@
      @ ensures \result >= 0;
      @ pure
      @*/
    public int getAttributesNumber() {
        return nameToFAttribute.size();
    }
    
    public Collection<FormalAttribute> getAttributes() {
        return Collections.unmodifiableCollection(nameToFAttribute.values());
    }
    
    /**
     * Return a read only iterator over the set of mapping from
     * the formal attributes representing alpha classes to the corresponding
     * objects sets.
     * @return a read only iterator over the set of mapping from alpha classes
     * to objects sets.
     */
    /*@
      @ ensures \result != null;
      @ pure
      @*/
    public Iterator<Entry<FormalAttribute, Set<FormalObject>>> classIterator() {
        Set<Entry<FormalAttribute, Set<FormalObject>>> entrySet = classAttrToObjectSet.entrySet();
        
        return Collections.unmodifiableSet(entrySet).iterator();
    }
    
    public Iterator<Couple<FormalObject, FormalAttribute>> iterator() {
        return new ObjToIntentMapIterator(fObjectToIntent);
    }
    /**
     * Returns the number of alpha classes in this context.
     * @return the number of alpha classes in this context.
     */
    /*@
      @ ensures \result >= 0;
      @ pure
      @*/
    public int getClassNumber() {
        return classAttrToObjectSet.size();
    }
    
    public MatrixBinaryRelationBuilder classToMatrixBinaryRelation(FormalAttribute classAttr) {
        FormalAttribute[] tabAttr = nameToFAttribute.values().toArray(new FormalAttribute[0]);
        FormalObject[] tabObj = classAttrToObjectSet.get(classAttr).toArray(new FormalObject[0]);
        MatrixBinaryRelationBuilder binRel = new MatrixBinaryRelationBuilder(tabObj.length, tabAttr.length);
        binRel.setName(classAttr.getName());
        
        int i = 0;
        for (FormalObject obj : tabObj) {
            try {
                binRel.replaceObject(i++, obj);
            } catch (BadInputDataException e) {
                // should not be
            }
        }
        
        i = 0;
        for (FormalAttribute att : tabAttr) {
            try {
                binRel.replaceAttribute(i++, att);
            } catch (BadInputDataException e) {
                // should not be
            }
        }
        
        i = 0;
        for (FormalObject obj : tabObj) {
           Set<FormalAttribute> objIntent = getIntent(obj);
           int j = 0;
           for (FormalAttribute att : tabAttr) {
                binRel.setRelation(i, j++, objIntent.contains(att));
             }
            i++;
        }
        return binRel;
    }

    /**
     * Test wether the specified attributeName corresponds to
     * a FormalAttribute currently present in this context.
     * @param attributeName the name of the attribute to search for.
     * @return true if this context contains an attribute with this name ; false
     * otherwise.
     */
    /*@
      @ requires attributeName != null;
      @ ensures \result ==> (attributeNumber() > 0);
      @ ensures (attributeNumber() == 0) ==> !\result;
      @ pure
      @*/
    public boolean containsAttributeForName(String attributeName) {
        return nameToFAttribute.containsKey(attributeName);
    }

    /**
     * Test wether the specified objectName corresponds to
     * a FormalObject currently known by this context.
     * @param objectName the name of the object to search for.
     * @return true if this context contains an object with this name ; false
     * otherwise.
     */
    /*@
      @ requires className != null;
      @ ensures \result ==> containsAttributeForName(className);
      @ ensures !containsAttributeForName(className) ==> !\result;
      @ pure
      @*/
    public boolean containsClassForName(String className) {
        FormalAttribute attr = getAttributeForName(className);
        if (attr == null) {
            return false;
        }
        return classAttrToObjectSet.containsKey(attr);
    }

    /**
     * Test wether the specified objectName corresponds to
     * a FormalObject currently known by this context.
     * @param objectName the name of the object to search for.
     * @return true if this context contains an object with this name ; false
     * otherwise.
     */
    /*@
      @ requires objectName != null;
      @ ensures \result ==> (objectNumber() > 0);
      @ ensures (objectNumber() == 0) ==> !\result;
      @ pure
      @*/
    public boolean containsObjectForName(String objectName) {
        return nameToFObject.containsKey(objectName);
    }

    /**
     * Return the FormalAttribute to wich this context maps the specified name. If such an attribute already
     * exists, this preexisting attribute is returned ; otherwise it returns null.
     * @param attributeName the name whose associated FormalAttribute is to be returned 
     * @return the FormalAttribute to wich this context maps the specified name or null if this context contains
     * no mapping for this attribute name.
     */
    /*@
    @ requires attributeName != null;
    @ {|
    @       requires containsAttributeForName(attributeName);
    @       ensures \result != null;
    @       ensures \result.getName().equals(attributeName);
    @   also
    @       requires !containsAttributeForName(attributeName);
    @       ensures \result == null;
    @ |}
    @ pure
    @*/
    public FormalAttribute getAttributeForName(String attributeName) {
        return nameToFAttribute.get(attributeName);
    }

    public Set<FormalAttribute> getClasses() {
        return Collections.unmodifiableSet(classAttrToObjectSet.keySet());
    }

    /**
     * Returns an unmodifiable view of the intent of the specified formal object. 
     * @param object the formal object for which the intent is to be returned.
     * @return An unmodifiable view of the intent of the specified formal object
     */
    /*@
      @ requires object != null;
      @ ensures \result != null;
      @ pure
      @*/
    public Set<FormalAttribute> getIntent(FormalObject object) {
        Set<FormalAttribute> intent = fObjectToIntent.get(object);
        if (intent == null) {
            return Collections.emptySet();
        }
        return Collections.unmodifiableSet(intent);
    }

    // Operations
    /**
     * Return the name of this context.
     * @return the name of this context.
     */
    /*@
      @ ensures \result != null;
      @
      @ pure
      @*/
    public String getName() {
        return name;
    }
    
    /**
     * Return the FormalObject to wich this context maps the specified name. If such an object already
     * exists, this preexisting object is returned ; otherwise it returns null.
     * @param objectName the name whose associated FormalObject is to be returned 
     * @return the FormalObject to wich this context maps the specified name or null if this context contains
     * no mapping for this object name.
     */
    /*@
      @ requires objectName != null;
      @ {|
      @     requires containsObjectForName(objectName);
      @     ensures \result != null;
      @     ensures \result.getName().equals(objectName);
      @   also
      @     requires !containsObjectForName(objectName);
      @     ensures \result == null;
      @ |}
      @ pure
      @*/
    public FormalObject getObjectForName(String objectName) {
        return nameToFObject.get(objectName);
    }
    
    /**
     * Return the Set of FormalObject to wich this context maps the specified
     * class attribute. If such an object Set already exists, this preexisting
     * object set is returned ; otherwise it returns null.
     * 
     * @param classAttr
     *            the class name whose associated set of FormalObject is to be
     *            returned
     * @return the set of FormalObject to wich this context maps the specified
     *         class attribute or null if this context contains no mapping for
     *         this class attribute.
     */
    /*@ 
      @ requires classAttr != null; 
      @ {| 
      @     requires containsClassForName(classAttr.getName()); 
      @     ensures \result != null; 
      @     ensures (\forall Object obj; \result.contains(obj); 
      @                                     obj instanceof FormalObject); 
      @ also 
      @     requires !containsClassForName(classAttr.getName()); 
      @     ensures \result == null; 
      @ |} 
      @ pure 
      @*/
    public Set<FormalObject> getObjectsForClass(FormalAttribute classAttr) {
        return Collections.unmodifiableSet(classAttrToObjectSet.get(classAttr));
    }
    
     public Collection<FormalObject> getObjects() {
         return Collections.unmodifiableCollection(nameToFObject.values());
     }
    /**
     * Returns the number of FormalObject in this context.
     * 
     * @return the number of FormalObject in this context.
     */
    /*@
      @ ensures \result >= 0;
      @ pure
      @*/
    public int getObjectsNumber() {
        return nameToFObject.size();
    }
}
