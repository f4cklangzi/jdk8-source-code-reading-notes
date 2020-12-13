/*
 * Copyright (c) 1997, 2013, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package java.util;

import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Hash table based implementation of the <tt>Map</tt> interface.  This
 * implementation provides all of the optional map operations, and permits
 * <tt>null</tt> values and the <tt>null</tt> key.  (The <tt>HashMap</tt>
 * class is roughly equivalent to <tt>Hashtable</tt>, except that it is
 * unsynchronized and permits nulls.)  This class makes no guarantees as to
 * the order of the map; in particular, it does not guarantee that the order
 * will remain constant over time.
 *
 * <p>This implementation provides constant-time performance for the basic
 * operations (<tt>get</tt> and <tt>put</tt>), assuming the hash function
 * disperses the elements properly among the buckets.  Iteration over
 * collection views requires time proportional to the "capacity" of the
 * <tt>HashMap</tt> instance (the number of buckets) plus its size (the number
 * of key-value mappings).  Thus, it's very important not to set the initial
 * capacity too high (or the load factor too low) if iteration performance is
 * important.
 *
 * <p>An instance of <tt>HashMap</tt> has two parameters that affect its
 * performance: <i>initial capacity</i> and <i>load factor</i>.  The
 * <i>capacity</i> is the number of buckets in the hash table, and the initial
 * capacity is simply the capacity at the time the hash table is created.  The
 * <i>load factor</i> is a measure of how full the hash table is allowed to
 * get before its capacity is automatically increased.  When the number of
 * entries in the hash table exceeds the product of the load factor and the
 * current capacity, the hash table is <i>rehashed</i> (that is, internal data
 * structures are rebuilt) so that the hash table has approximately twice the
 * number of buckets.
 *
 * <p>As a general rule, the default load factor (.75) offers a good
 * tradeoff between time and space costs.  Higher values decrease the
 * space overhead but increase the lookup cost (reflected in most of
 * the operations of the <tt>HashMap</tt> class, including
 * <tt>get</tt> and <tt>put</tt>).  The expected number of entries in
 * the map and its load factor should be taken into account when
 * setting its initial capacity, so as to minimize the number of
 * rehash operations.  If the initial capacity is greater than the
 * maximum number of entries divided by the load factor, no rehash
 * operations will ever occur.
 *
 * <p>If many mappings are to be stored in a <tt>HashMap</tt>
 * instance, creating it with a sufficiently large capacity will allow
 * the mappings to be stored more efficiently than letting it perform
 * automatic rehashing as needed to grow the table.  Note that using
 * many keys with the same {@code hashCode()} is a sure way to slow
 * down performance of any hash table. To ameliorate impact, when keys
 * are {@link Comparable}, this class may use comparison order among
 * keys to help break ties.
 *
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access a hash map concurrently, and at least one of
 * the threads modifies the map structurally, it <i>must</i> be
 * synchronized externally.  (A structural modification is any operation
 * that adds or deletes one or more mappings; merely changing the value
 * associated with a key that an instance already contains is not a
 * structural modification.)  This is typically accomplished by
 * synchronizing on some object that naturally encapsulates the map.
 *
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedMap Collections.synchronizedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map:<pre>
 *   Map m = Collections.synchronizedMap(new HashMap(...));</pre>
 *
 * <p>The iterators returned by all of this class's "collection view methods"
 * are <i>fail-fast</i>: if the map is structurally modified at any time after
 * the iterator is created, in any way except through the iterator's own
 * <tt>remove</tt> method, the iterator will throw a
 * {@link ConcurrentModificationException}.  Thus, in the face of concurrent
 * modification, the iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the
 * future.
 *
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw <tt>ConcurrentModificationException</tt> on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness: <i>the fail-fast behavior of iterators
 * should be used only to detect bugs.</i>
 *
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 *
 * @author  Doug Lea
 * @author  Josh Bloch
 * @author  Arthur van Hoff
 * @author  Neal Gafter
 * @see     Object#hashCode()
 * @see     Collection
 * @see     Map
 * @see     TreeMap
 * @see     Hashtable
 * @since   1.2
 */
public class HashMap<K,V> extends AbstractMap<K,V>
    implements Map<K,V>, Cloneable, Serializable {

    private static final long serialVersionUID = 362498820763181265L;

    /*
     * Implementation notes.
     *
     * This map usually acts as a binned (bucketed) hash table, but
     * when bins get too large, they are transformed into bins of
     * TreeNodes, each structured similarly to those in
     * java.util.TreeMap. Most methods try to use normal bins, but
     * relay to TreeNode methods when applicable (simply by checking
     * instanceof a node).  Bins of TreeNodes may be traversed and
     * used like any others, but additionally support faster lookup
     * when overpopulated. However, since the vast majority of bins in
     * normal use are not overpopulated, checking for existence of
     * tree bins may be delayed in the course of table methods.
     *
     * Tree bins (i.e., bins whose elements are all TreeNodes) are
     * ordered primarily by hashCode, but in the case of ties, if two
     * elements are of the same "class C implements Comparable<C>",
     * type then their compareTo method is used for ordering. (We
     * conservatively check generic types via reflection to validate
     * this -- see method comparableClassFor).  The added complexity
     * of tree bins is worthwhile in providing worst-case O(log n)
     * operations when keys either have distinct hashes or are
     * orderable, Thus, performance degrades gracefully under
     * accidental or malicious usages in which hashCode() methods
     * return values that are poorly distributed, as well as those in
     * which many keys share a hashCode, so long as they are also
     * Comparable. (If neither of these apply, we may waste about a
     * factor of two in time and space compared to taking no
     * precautions. But the only known cases stem from poor user
     * programming practices that are already so slow that this makes
     * little difference.)
     *
     * Because TreeNodes are about twice the size of regular nodes, we
     * use them only when bins contain enough nodes to warrant use
     * (see TREEIFY_THRESHOLD). And when they become too small (due to
     * removal or resizing) they are converted back to plain bins.  In
     * usages with well-distributed user hashCodes, tree bins are
     * rarely used.  Ideally, under random hashCodes, the frequency of
     * nodes in bins follows a Poisson distribution
     * (http://en.wikipedia.org/wiki/Poisson_distribution) with a
     * parameter of about 0.5 on average for the default resizing
     * threshold of 0.75, although with a large variance because of
     * resizing granularity. Ignoring variance, the expected
     * occurrences of list size k are (exp(-0.5) * pow(0.5, k) /
     * factorial(k)). The first values are:
     *
     * 0:    0.60653066
     * 1:    0.30326533
     * 2:    0.07581633
     * 3:    0.01263606
     * 4:    0.00157952
     * 5:    0.00015795
     * 6:    0.00001316
     * 7:    0.00000094
     * 8:    0.00000006
     * more: less than 1 in ten million
     *
     * The root of a tree bin is normally its first node.  However,
     * sometimes (currently only upon Iterator.remove), the root might
     * be elsewhere, but can be recovered following parent links
     * (method TreeNode.root()).
     *
     * All applicable internal methods accept a hash code as an
     * argument (as normally supplied from a public method), allowing
     * them to call each other without recomputing user hashCodes.
     * Most internal methods also accept a "tab" argument, that is
     * normally the current table, but may be a new or old one when
     * resizing or converting.
     *
     * When bin lists are treeified, split, or untreeified, we keep
     * them in the same relative access/traversal order (i.e., field
     * Node.next) to better preserve locality, and to slightly
     * simplify handling of splits and traversals that invoke
     * iterator.remove. When using comparators on insertion, to keep a
     * total ordering (or as close as is required here) across
     * rebalancings, we compare classes and identityHashCodes as
     * tie-breakers.
     *
     * The use and transitions among plain vs tree modes is
     * complicated by the existence of subclass LinkedHashMap. See
     * below for hook methods defined to be invoked upon insertion,
     * removal and access that allow LinkedHashMap internals to
     * otherwise remain independent of these mechanics. (This also
     * requires that a map instance be passed to some utility methods
     * that may create new nodes.)
     *
     * The concurrent-programming-like SSA-based coding style helps
     * avoid aliasing errors amid all of the twisty pointer operations.
     */

    /**
     * The default initial capacity - MUST be a power of two.
     * 缺省的table长度 1*2^4=16
     */
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16

    /**
     * The maximum capacity, used if a higher value is implicitly specified
     * by either of the constructors with arguments.
     * MUST be a power of two <= 1<<30.
     * table数组最大长度 1*2^30
     */
    static final int MAXIMUM_CAPACITY = 1 << 30;

    /**
     * The load factor used when none specified in constructor.
     * 缺省的负载因子
     */
    static final float DEFAULT_LOAD_FACTOR = 0.75f;

    /**
     * The bin count threshold for using a tree rather than list for a
     * bin.  Bins are converted to trees when adding an element to a
     * bin with at least this many nodes. The value must be greater
     * than 2 and should be at least 8 to mesh with assumptions in
     * tree removal about conversion back to plain bins upon
     * shrinkage.
     * 链表树化的一个条件 链表长度(包含头结点) >= 9就树化
     */
    static final int TREEIFY_THRESHOLD = 8;

    /**
     * The bin count threshold for untreeifying a (split) bin during a
     * resize operation. Should be less than TREEIFY_THRESHOLD, and at
     * most 6 to mesh with shrinkage detection under removal.
     * 树化恢复阈值 链表长度 <= 6就恢复成链表
     */
    static final int UNTREEIFY_THRESHOLD = 6;

    /**
     * The smallest table capacity for which bins may be treeified.
     * (Otherwise the table is resized if too many nodes in a bin.)
     * Should be at least 4 * TREEIFY_THRESHOLD to avoid conflicts
     * between resizing and treeification thresholds.
     * 链表树化的另一个条件 数组长度>=64才进行树化
     */
    static final int MIN_TREEIFY_CAPACITY = 64;

    /**
     * Basic hash bin node, used for most entries.  (See below for
     * TreeNode subclass, and in LinkedHashMap for its Entry subclass.)
     */
    static class Node<K,V> implements Map.Entry<K,V> {
        final int hash;
        final K key;
        V value;
        Node<K,V> next;

        Node(int hash, K key, V value, Node<K,V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey()        { return key; }
        public final V getValue()      { return value; }
        public final String toString() { return key + "=" + value; }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>)o;
                if (Objects.equals(key, e.getKey()) &&
                    Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }

    /* ---------------- Static utilities -------------- */

    /**
     * Computes key.hashCode() and spreads (XORs) higher bits of hash
     * to lower.  Because the table uses power-of-two masking, sets of
     * hashes that vary only in bits above the current mask will
     * always collide. (Among known examples are sets of Float keys
     * holding consecutive whole numbers in small tables.)  So we
     * apply a transform that spreads the impact of higher bits
     * downward. There is a tradeoff between speed, utility, and
     * quality of bit-spreading. Because many common sets of hashes
     * are already reasonably distributed (so don't benefit from
     * spreading), and because we use trees to handle large sets of
     * collisions in bins, we just XOR some shifted bits in the
     * cheapest possible way to reduce systematic lossage, as well as
     * to incorporate impact of the highest bits that would otherwise
     * never be used in index calculations because of table bounds.
     * hash扰动函数
     */
    static final int hash(Object key) {
        int h;
        // ^ 异或：相同为0不同为1
        // >>> 无符号右移：左边补0
        // null的hash永远是0，其他的把key的高16位和低16位进行异或，这样可以保证在求模时高位的变化也能够影响到结果
        // 求模时是hash&(size-1) 当table数组长度比较小时，后面肯定全是1，但是高位都是0，这样结果就是只有低位参与了运算，
        // 高位和0进行与操作结果还是0，但是把高位的特征也混合到低位中来就可以让hash高位也能对求模的结果产生影响，增加随机性
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }

    /**
     * Returns x's Class if it is of the form "class C implements
     * Comparable<C>", else null.
     * 如果对象x的类是C，如果C实现了Comparable<C>接口，那么返回C，否则返回null
     * 看看x的class是否 implements  Comparable<x的class>
     */
    static Class<?> comparableClassFor(Object x) {
        // 如果x实现了comparable接口
        if (x instanceof Comparable) {
            // c表示x的class对象
            // ts表示x实现的接口列表(泛型接口附带泛型信息)
            // t表示泛型接口
            // p表示泛型接口t的原始类型
            Class<?> c; Type[] ts, as; Type t; ParameterizedType p;
            // 如果是字符串类型直接返回，因为字符串实现了comparable接口
            if ((c = x.getClass()) == String.class) // bypass checks
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {
                // 遍历c实现的接口
                for (int i = 0; i < ts.length; ++i) {
                    // 如果接口是泛型类并且
                    // 该泛型接口的原始类型是Comparable接口并且
                    // 该Comparable接口只定义了一个泛型参数并且
                    // 这个泛型参数就是c
                    if (((t = ts[i]) instanceof ParameterizedType) &&
                        ((p = (ParameterizedType)t).getRawType() ==
                         Comparable.class) &&
                        (as = p.getActualTypeArguments()) != null &&
                        as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        // x没有实现comparable直接返回null
        return null;
    }

    /**
     * Returns k.compareTo(x) if x matches kc (k's screened comparable
     * class), else 0.
     * 如果x所属的类是kc，返回k.compareTo(x)的比较结果
     */
    @SuppressWarnings({"rawtypes","unchecked"}) // for cast to Comparable
    static int compareComparables(Class<?> kc, Object k, Object x) {
        // 如果x为空，或者其所属的类不是kc，返回0
        // 否则返回k.compareTo(x)的比较结果
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable)k).compareTo(x));
    }

    /**
     * Returns a power of two size for the given target capacity.
     */
    static final int tableSizeFor(int cap) {
        int n = cap - 1;
        // 把n二进制从高位开始第一个1后面的所有位全都变成1，这样肯定是一个大于n的2的次方数
        // 0010 1101 001 -> 0011 1111 1111
        n |= n >>> 1;
        n |= n >>> 2;
        n |= n >>> 4;
        n |= n >>> 8;
        n |= n >>> 16;
        return (n < 0) ? 1 : (n >= MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : n + 1;
    }

    /* ---------------- Fields -------------- */

    /**
     * The table, initialized on first use, and resized as
     * necessary. When allocated, length is always a power of two.
     * (We also tolerate length zero in some operations to allow
     * bootstrapping mechanics that are currently not needed.)
     * 存放Node元素的数组
     */
    transient Node<K,V>[] table;

    /**
     * Holds cached entrySet(). Note that AbstractMap fields are used
     * for keySet() and values().
     */
    transient Set<Map.Entry<K,V>> entrySet;

    /**
     * The number of key-value mappings contained in this map.
     * HashMap中元素个数(包含数组中的和链表红黑树中的)
     */
    transient int size;

    /**
     * The number of times this HashMap has been structurally modified
     * Structural modifications are those that change the number of mappings in
     * the HashMap or otherwise modify its internal structure (e.g.,
     * rehash).  This field is used to make iterators on Collection-views of
     * the HashMap fail-fast.  (See ConcurrentModificationException).
     * HashMap结构修改次数
     */
    transient int modCount;

    /**
     * The next size value at which to resize (capacity * load factor).
     * 扩容阈值：当HashMap中的元素个数size > 这个阈值table数组就会进行扩容，元素个数是包含链表/红黑树上的
     * = capacity * loadFactor
     * @serial
     */
    // (The javadoc description is true upon serialization.
    // Additionally, if the table array has not been allocated, this
    // field holds the initial array capacity, or zero signifying
    // DEFAULT_INITIAL_CAPACITY.)
    int threshold;

    /**
     * The load factor for the hash table.
     * 负载因子：用于计算threshold
     * @serial
     */
    final float loadFactor;

    /* ---------------- Public operations -------------- */

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and load factor.
     *
     * @param  initialCapacity the initial capacity
     * @param  loadFactor      the load factor
     * @throws IllegalArgumentException if the initial capacity is negative
     *         or the load factor is nonpositive
     */
    public HashMap(int initialCapacity, float loadFactor) {
        // 0 <= initialCapacity <= 2^30
        if (initialCapacity < 0)
            throw new IllegalArgumentException("Illegal initial capacity: " +
                                               initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY)
            initialCapacity = MAXIMUM_CAPACITY;
        // 0 < loadFactor并且必须是浮点数，这里可以大于1，不会报错，只是会影响性能
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new IllegalArgumentException("Illegal load factor: " +
                                               loadFactor);
        // 给负载因子赋值
        this.loadFactor = loadFactor;
        // 计算扩容阈值，返回一个>=initialCapacity的数字，并且是2的次方数
        // 这里没有把计算的结果乘以负载因子，因为后面会resize()方法会重新初始化threshold
        this.threshold = tableSizeFor(initialCapacity);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the specified initial
     * capacity and the default load factor (0.75).
     *
     * @param  initialCapacity the initial capacity.
     * @throws IllegalArgumentException if the initial capacity is negative.
     */
    public HashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Constructs an empty <tt>HashMap</tt> with the default initial capacity
     * (16) and the default load factor (0.75).
     */
    public HashMap() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }

    /**
     * Constructs a new <tt>HashMap</tt> with the same mappings as the
     * specified <tt>Map</tt>.  The <tt>HashMap</tt> is created with
     * default load factor (0.75) and an initial capacity sufficient to
     * hold the mappings in the specified <tt>Map</tt>.
     *
     * @param   m the map whose mappings are to be placed in this map
     * @throws  NullPointerException if the specified map is null
     */
    public HashMap(Map<? extends K, ? extends V> m) {
        this.loadFactor = DEFAULT_LOAD_FACTOR;
        putMapEntries(m, false);
    }

    /**
     * Implements Map.putAll and Map constructor
     *
     * @param m the map
     * @param evict false when initially constructing this map, else
     * true (relayed to method afterNodeInsertion).
     */
    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();
        if (s > 0) {
            if (table == null) { // pre-size
                float ft = ((float)s / loadFactor) + 1.0F;
                int t = ((ft < (float)MAXIMUM_CAPACITY) ?
                         (int)ft : MAXIMUM_CAPACITY);
                if (t > threshold)
                    threshold = tableSizeFor(t);
            }
            else if (s > threshold)
                resize();
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size() {
        return size;
    }

    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     *
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty() {
        return size == 0;
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code (key==null ? k==null :
     * key.equals(k))}, then this method returns {@code v}; otherwise
     * it returns {@code null}.  (There can be at most one such mapping.)
     *
     * <p>A return value of {@code null} does not <i>necessarily</i>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @see #put(Object, Object)
     */
    public V get(Object key) {
        Node<K,V> e;
        // 通过key的hash和key查找数组下标处hash和key同时相等的(相等的判断条件是==或者equals)
        return (e = getNode(hash(key), key)) == null ? null : e.value;
    }

    /**
     * Implements Map.get and related methods
     * 通过hash和key查找Node
     *
     * @param hash hash for key
     * @param key the key
     * @return the node, or null if none
     */
    final Node<K,V> getNode(int hash, Object key) {
        // tab代表able数组
        // first代表hash在table数组下标处的第一个节点
        // e代表在红黑树或者数组中查找时的当前遍历节点
        // n代表table数组的长度
        // k代表e的key
        Node<K,V>[] tab; Node<K,V> first, e; int n; K k;
        // 同时满足以下3个条件才进行查找：
        // table数组已经初始化
        // table数组长度大于0
        // hash对应的数组下标处有节点
        if ((tab = table) != null && (n = tab.length) > 0 &&
            (first = tab[(n - 1) & hash]) != null) {
            // 同一个下标处的元素hash不一定都相等，因此比较hash和key是否相等，相等(==或equals)就算找到
            if (first.hash == hash && // always check first node
                ((k = first.key) == key || (key != null && key.equals(k))))
                return first;
            // 如果数组下标处是链表则继续查找
            if ((e = first.next) != null) {
                // 红黑树的情况直接调用红黑树的查找方法进行查找
                if (first instanceof TreeNode)
                    return ((TreeNode<K,V>)first).getTreeNode(hash, key);
                // 链表的情况就遍历链表进行查找
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k))))
                        return e;
                } while ((e = e.next) != null);
            }
        }
        // 未找到返回null
        return null;
    }

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the
     * specified key.
     *
     * @param   key   The key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified
     * key.
     */
    public boolean containsKey(Object key) {
        return getNode(hash(key), key) != null;
    }

    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old
     * value is replaced.
     *
     * @param key key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    /**
     * Implements Map.put and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @param value the value to put
     * @param onlyIfAbsent if true, don't change existing value 传true表示这个key存在时不替换
     * @param evict if false, the table is in creation mode.
     * @return previous value, or null if none
     */
    final V putVal(int hash, K key, V value, boolean onlyIfAbsent,
                   boolean evict) {
        // tab表示HashMap的table数组
        // p表示数组中的一个Node
        // n表示数组的长度
        // i表示寻址的结果(数组下标)
        Node<K,V>[] tab; Node<K,V> p; int n, i;
        // 延迟初始化，第一次调用putVal时进行数组初始化
        if ((tab = table) == null || (n = tab.length) == 0)
            // 第一次初始化resize()返回一个空数组
            n = (tab = resize()).length;
        // 计算hash在数组中应该存放的下标并赋值给p 判断此位置是否有Node
        if ((p = tab[i = (n - 1) & hash]) == null)
            // 此位置没有Node则新建一个普通Node放到数组此位置
            tab[i] = newNode(hash, key, value, null);
        else {
            // e表示HashMap中和待添加Node相等的Node
            // k表示临时key变量
            Node<K,V> e; K k;
            // 如果已经存在的Node的hash和key都和要存放的Node相等(HashMap判断相等是判断key的hash和key本身是否同时相等)
            if (p.hash == hash &&
                ((k = p.key) == key || (key != null && key.equals(k))))
                // 则把原来的值赋值给e
                e = p;
            // 如果已经存在的Node是一棵红黑树
            else if (p instanceof TreeNode)
                e = ((TreeNode<K,V>)p).putTreeVal(this, tab, hash, key, value);
            // 如果已经存在的Node是链表头
            else {
                // 遍历链表 binCount表示链表除开头结点的个数(binCount为0的时候就表示头结点)
                for (int binCount = 0; ; ++binCount) {
                    // 到达链表尾的时候就准备插入新Node到链表尾(尾插法，这里在JDK1.7中是头插法，但是有bug)
                    if ((e = p.next) == null) {
                        // 创建新Node并插入到链表中
                        p.next = newNode(hash, key, value, null);
                        // 如果除开链表头的链表个数 >= 7 即整个链表长度 >= 8(这里的链表长度是新节点插入之前长度，也就是当链表长度
                        // > = 9时就进行树化)
                        if (binCount >= TREEIFY_THRESHOLD - 1) // -1 for 1st
                            // 对table数组上存放hash的位置上的链表进行树化
                            treeifyBin(tab, hash);
                        break;
                    }
                    // 遍历过程中判断链表中有没有和待添加Node相同的
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k))))
                        // 如果待插入Node存在于链表中则终端遍历 此时e就是链表中和待添加Node相等的Node
                        break;
                    // 移动遍历指针继续遍历
                    p = e;
                }
            }
            // 如果HashMap中已经存在和待添加Node相同的Node
            if (e != null) { // existing mapping for key
                // 保存原来Node中的值
                V oldValue = e.value;
                // putIfAbsent传入的onlyIfAbsent为true表示不存在则添加
                // 如果不是"存在则不替换"或者原来Node的值为null
                if (!onlyIfAbsent || oldValue == null)
                    // 用新值替换旧值
                    e.value = value;
                // 子类实现方法
                afterNodeAccess(e);
                // 返回旧值(此处没有修改modCount，也就是说替换一个值不会导致fail-fast)
                return oldValue;
            }
        }
        ++modCount;
        // 如果添加后的Node个数大于扩容阈值
        if (++size > threshold)
            // 扩容
            resize();
        // 子类实现方法
        afterNodeInsertion(evict);
        // 没有替换的情况下返回null
        return null;
    }

    /**
     * Initializes or doubles table size.  If null, allocates in
     * accord with initial capacity target held in field threshold.
     * Otherwise, because we are using power-of-two expansion, the
     * elements from each bin must either stay at same index, or move
     * with a power of two offset in the new table.
     *
     * @return the table
     */
    final Node<K,V>[] resize() {
        // oldTab代表扩容前的table数组
        Node<K,V>[] oldTab = table;
        // oldCap代表扩容前的数组长度
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        // oldThr代表扩容前的扩容阈值
        int oldThr = threshold;
        // 新数组容量和新的扩容阈值都默认为0
        int newCap, newThr = 0;
        // 这里分三种情况
        // 1.原数组已经存放有元素(已经在putVal()初始化扩容过)
        // 2.原数组没有元素但是原来的threshold已经有值(使用带参数的构造方法创建了HashMap，第一次扩容，因为在构造方法里面
        // 只设置了负载因子和threshold，并且将threshold设置为了table的大小)
        // 3.原数组没有元素并且原来的threshold也没有初始化(使用无参构造方法创建的HashMap，这种只设置了负载因子为默认的0.75f)
        if (oldCap > 0) {
            // 如果数组长度已经达到了2^30那么将扩容阈值设置为Integer最大值并返回
            if (oldCap >= MAXIMUM_CAPACITY) {
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            // 如果扩容后的数组长度小于允许的最大数组长度2^30 并且 扩容前的数组长度大于等于16则把新数组长度设置为扩容前的2倍
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY &&
                     oldCap >= DEFAULT_INITIAL_CAPACITY)
                // 左移一位就是*2
                newThr = oldThr << 1; // double threshold
        }
        else if (oldThr > 0) // initial capacity was placed in threshold
            // 构造函数里面呢把threshold设置成了数组长度，这里要赋值给数组长度，此时newThr依旧是默认的0,下面重新计算值
            newCap = oldThr;
        else {               // zero initial threshold signifies using defaults
            //无参构造方法只设置了负载因子，新数组长度就是默认的16，新的扩容阈值就是12
            newCap = DEFAULT_INITIAL_CAPACITY;
            newThr = (int)(DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);
        }
        // 走到这一步新的扩容阈值还没赋值说明是扩容前的数组长度小于16或者此时的扩容阈值就是存放的临时数组长度
        // 这是新的数组长度已经确定了，可以直接使用新的数组长度计算扩容阈值
        if (newThr == 0) {
            // 计算新的扩容阈值
            float ft = (float)newCap * loadFactor;
            // 新的数组长度小于最大长度并且新的扩容阈值小于最大数组长度 新的扩容阈值就使用计算的值，否则使用Integer最大值
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float)MAXIMUM_CAPACITY ?
                      (int)ft : Integer.MAX_VALUE);
        }
        // 设置新的扩容阈值到HashMap上
        threshold = newThr;
        // 创建一个新数组长度的空数组
        @SuppressWarnings({"rawtypes","unchecked"})
            Node<K,V>[] newTab = (Node<K,V>[])new Node[newCap];
        // 设置新创建的空数组到HashMap上
        table = newTab;
        // 第一次初始化直接返回扩容后的新数组
        if (oldTab != null) {
            // 不是第一次则要把扩容前数组的值全部转移到新数组中来，需要重新确定每个元素的位置
            for (int j = 0; j < oldCap; ++j) {
                // 遍历数组来获得每个元素，用e保存数组上的元素
                Node<K,V> e;
                // 如果当前数组位置有元素才进行转移
                if ((e = oldTab[j]) != null) {
                    // 释放掉扩容前数组上的元素
                    oldTab[j] = null;
                    // 这里分3中情况
                    // 1.数组下标处存放的是一个next指针指向null的元素(该位置没有发生hash冲突)
                    // 2.数组下标处存放的是一棵红黑树节点
                    // 3.数组下标处存放的是一个还没树化的链表
                    if (e.next == null)
                        // 没有冲突的直接把此处的元素重新计算下标并放入新数组中
                        newTab[e.hash & (newCap - 1)] = e;
                    else if (e instanceof TreeNode)
                        ((TreeNode<K,V>)e).split(this, newTab, j, oldCap);
                    else { // preserve order
                        // 链表的话需要把链表拆分成两个链表，一个链表还在原来的位置，另一个链表在原来位置+扩容前数组大小处
                        // loHead和loTail分别代表位置不变的链表头指针和尾指针
                        // hiHead和hiTail分别代表位置变化的链表头指针和尾指针
                        Node<K,V> loHead = null, loTail = null;
                        Node<K,V> hiHead = null, hiTail = null;
                        // next代表遍历原链表过程中的正在遍历的元素
                        Node<K,V> next;
                        // 遍历原来的链表
                        do {
                            // 遍历指针后移，这句应该放在循环的结尾(循环中没有使用next所以放哪儿都不影响运行)
                            next = e.next;
                            // 这里使用e.hash & oldCap替代取模算法e.hash & (newCap-1)
                            // 例如：
                            // 如果之前的容量是4，则取模就是拿后面2位，
                            // 新容量是8则取模就是拿后面3位，因此判断是不是在原位置就直接看从后往前第3位，也就是拿8直接和4进行与运算，
                            // 因为4=100，拿到的就是第三位，第三位如果是0，那么8 & 7的时候拿的后三位和8 & 3拿的后两位就没区别了，
                            // 肯定取模结果也一样，因此通过判断第三位是否为0就一个取模的位置是否在原来位置了
                            if ((e.hash & oldCap) == 0) {
                                // 位置不变的串成一个新的单向链表lo
                                if (loTail == null)
                                    loHead = e;
                                else
                                    loTail.next = e;
                                loTail = e;
                            }
                            else {
                                // 位置改变的串成一个新的单向链表hi
                                if (hiTail == null)
                                    hiHead = e;
                                else
                                    hiTail.next = e;
                                hiTail = e;
                            }
                        } while ((e = next) != null);
                        // 存在位置不变得节点
                        if (loTail != null) {
                            // 链表尾的next指针置为null(这个节点之前不一定是尾节点，所以next指针可能不是null)
                            loTail.next = null;
                            // 新数组的原位置放位置不变节点链表头
                            newTab[j] = loHead;
                        }
                        // 存在位置改变的节点
                        if (hiTail != null) {
                            hiTail.next = null;
                            // 位置改变节点的链表头放在原位置+扩容前数组大小处
                            newTab[j + oldCap] = hiHead;
                        }
                    }
                }
            }
        }
        // 返回扩容后的新数组
        return newTab;
    }

    /**
     * Replaces all linked nodes in bin at index for given hash unless
     * table is too small, in which case resizes instead.
     * 将hash所在位置的冲突链表元素进行树化
     */
    final void treeifyBin(Node<K,V>[] tab, int hash) {
        // n表示table数组长度
        // index表示当前hash取模后的下标位置
        // e表示链表上的一个Node节点，初始化为链表头结点，循环过程中向后移动
        int n, index; Node<K,V> e;
        // table数组里面还没有元素放入或者table数组的长度小于64则只进行扩容操作，不进行树化操作
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            // 扩容
            resize();
        // 如果当前hash的位置有元素就进行树化操作
        else if ((e = tab[index = (n - 1) & hash]) != null) {
            // hd代表链表头指针
            // tl代表链表尾指针
            TreeNode<K,V> hd = null, tl = null;
            // 从头开始遍历链表，将链表节点转换为红黑树节点，同时用双向链表连接起来
            do {
                // 将链表节点转换为红黑树节点，同时next指针指向null
                TreeNode<K,V> p = replacementTreeNode(e, null);
                // 如果还没有链表尾则说明当前遍历的是链表第一个节点
                if (tl == null)
                    // 链表头指向当前p节点
                    hd = p;
                else {
                    // 把p节点放到链表尾
                    p.prev = tl;
                    tl.next = p;
                }
                // 链表尾指针指向当前元素
                tl = p;
                // e节点指向链表下一个继续循环，直到遍历到链表尾
            } while ((e = e.next) != null);
            // 如果新的链表存在就把新的红黑树链表头指针放到数组上，把红黑树节点构成一棵红黑树
            if ((tab[index] = hd) != null)
                hd.treeify(tab);
        }
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings will replace any mappings that this map had for
     * any of the keys currently in the specified map.
     *
     * @param m mappings to be stored in this map
     * @throws NullPointerException if the specified map is null
     */
    public void putAll(Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }

    /**
     * Removes the mapping for the specified key from this map if present.
     *
     * @param  key key whose mapping is to be removed from the map
     * @return the previous value associated with <tt>key</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>key</tt>.
     *         (A <tt>null</tt> return can also indicate that the map
     *         previously associated <tt>null</tt> with <tt>key</tt>.)
     */
    public V remove(Object key) {
        Node<K,V> e;
        return (e = removeNode(hash(key), key, null, false, true)) == null ?
            null : e.value;
    }

    /**
     * Implements Map.remove and related methods
     *
     * @param hash hash for key
     * @param key the key
     * @param value the value to match if matchValue, else ignored
     * @param matchValue if true only remove if value is equal
     * @param movable if false do not move other nodes while removing
     * @return the node, or null if none
     */
    final Node<K,V> removeNode(int hash, Object key, Object value,
                               boolean matchValue, boolean movable) {
        // tab代表table数组
        // p代表移除hash对应数组下标的第一个值
        // n代表table数组长度
        // index代表hash对应的数组下标
        Node<K,V>[] tab; Node<K,V> p; int n, index;
        // 数组下标处有节点再继续操作
        if ((tab = table) != null && (n = tab.length) > 0 &&
            (p = tab[index = (n - 1) & hash]) != null) {
            // node代表找到的将要删除的节点
            // e代表链表/红黑树遍历过程中的节点
            Node<K,V> node = null, e; K k; V v;
            // 下面是查找节点的过程
            if (p.hash == hash &&
                ((k = p.key) == key || (key != null && key.equals(k))))
                node = p;
            else if ((e = p.next) != null) {
                if (p instanceof TreeNode)
                    node = ((TreeNode<K,V>)p).getTreeNode(hash, key);
                else {
                    do {
                        if (e.hash == hash &&
                            ((k = e.key) == key ||
                             (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }
            // 两个条件满足才删除：
            // 节点存在
            // matchValue==false 或 value相等
            if (node != null && (!matchValue || (v = node.value) == value ||
                                 (value != null && value.equals(v)))) {
                // 节点是红黑树节点则调用红黑树的方法 删除
                if (node instanceof TreeNode)
                    ((TreeNode<K,V>)node).removeTreeNode(this, tab, movable);
                // 数组下标处只有一个节点的情况，此时node.next就是null
                else if (node == p)
                    tab[index] = node.next;
                // p此时是node的前驱节点，前驱节点的后继指针直接指向node的后继节点，略过node表示删除
                else
                    p.next = node.next;
                ++modCount;
                // 节点数减一
                --size;
                afterNodeRemoval(node);
                // 返回被删除的节点
                return node;
            }
        }
        // 没找到元素返回null
        return null;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear() {
        Node<K,V>[] tab;
        modCount++;
        if ((tab = table) != null && size > 0) {
            // size置0
            size = 0;
            // 循环遍历清空table数组
            for (int i = 0; i < tab.length; ++i)
                tab[i] = null;
        }
    }

    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if this map maps one or more keys to the
     *         specified value
     */
    public boolean containsValue(Object value) {
        Node<K,V>[] tab; V v;
        // table数组没有初始化或者节点个数为0直接返回false
        if ((tab = table) != null && size > 0) {
            // 遍历table数组
            for (int i = 0; i < tab.length; ++i) {
                // 把数组中每个节点都当成链表进行遍历查找
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    if ((v = e.value) == value ||
                        (value != null && value.equals(v)))
                        return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation), the results of
     * the iteration are undefined.  The set supports element removal,
     * which removes the corresponding mapping from the map, via the
     * <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt>, and <tt>clear</tt>
     * operations.  It does not support the <tt>add</tt> or <tt>addAll</tt>
     * operations.
     *
     * @return a set view of the keys contained in this map
     */
    public Set<K> keySet() {
        Set<K> ks;
        return (ks = keySet) == null ? (keySet = new KeySet()) : ks;
    }

    final class KeySet extends AbstractSet<K> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<K> iterator()     { return new KeyIterator(); }
        public final boolean contains(Object o) { return containsKey(o); }
        public final boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }
        public final Spliterator<K> spliterator() {
            return new KeySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super K> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.key);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own <tt>remove</tt> operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a view of the values contained in this map
     */
    public Collection<V> values() {
        Collection<V> vs;
        return (vs = values) == null ? (values = new Values()) : vs;
    }

    final class Values extends AbstractCollection<V> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<V> iterator()     { return new ValueIterator(); }
        public final boolean contains(Object o) { return containsValue(o); }
        public final Spliterator<V> spliterator() {
            return new ValueSpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super V> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e.value);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own <tt>remove</tt> operation, or through the
     * <tt>setValue</tt> operation on a map entry returned by the
     * iterator) the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Set.remove</tt>, <tt>removeAll</tt>, <tt>retainAll</tt> and
     * <tt>clear</tt> operations.  It does not support the
     * <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * @return a set view of the mappings contained in this map
     */
    public Set<Map.Entry<K,V>> entrySet() {
        Set<Map.Entry<K,V>> es;
        return (es = entrySet) == null ? (entrySet = new EntrySet()) : es;
    }

    final class EntrySet extends AbstractSet<Map.Entry<K,V>> {
        public final int size()                 { return size; }
        public final void clear()               { HashMap.this.clear(); }
        public final Iterator<Map.Entry<K,V>> iterator() {
            return new EntryIterator();
        }
        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?,?> e = (Map.Entry<?,?>) o;
            Object key = e.getKey();
            Node<K,V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }
        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }
        public final Spliterator<Map.Entry<K,V>> spliterator() {
            return new EntrySpliterator<>(HashMap.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super Map.Entry<K,V>> action) {
            Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }

    // Overrides of JDK8 Map extension methods

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        Node<K,V> e;
        return (e = getNode(hash(key), key)) == null ? defaultValue : e.value;
    }

    @Override
    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }

    @Override
    public boolean remove(Object key, Object value) {
        // 只有通过key查找到的节点的value和给定value相等时才删除
        return removeNode(hash(key), key, value, true, true) != null;
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        Node<K,V> e; V v;
        // 查找到的node节点的value等于给定旧值才进行替换
        if ((e = getNode(hash(key), key)) != null &&
            ((v = e.value) == oldValue || (v != null && v.equals(oldValue)))) {
            e.value = newValue;
            afterNodeAccess(e);
            return true;
        }
        return false;
    }

    @Override
    public V replace(K key, V value) {
        // e表示通过key查找到的节点
        Node<K,V> e;
        if ((e = getNode(hash(key), key)) != null) {
            V oldValue = e.value;
            // 替换值
            e.value = value;
            afterNodeAccess(e);
            // 返回被替换的旧值
            return oldValue;
        }
        // 没找到直接返回null
        return null;
    }

    @Override
    public V computeIfAbsent(K key,
                             Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
            V oldValue;
            if (old != null && (oldValue = old.value) != null) {
                afterNodeAccess(old);
                return oldValue;
            }
        }
        V v = mappingFunction.apply(key);
        if (v == null) {
            return null;
        } else if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        else if (t != null)
            t.putTreeVal(this, tab, hash, key, v);
        else {
            tab[i] = newNode(hash, key, v, first);
            if (binCount >= TREEIFY_THRESHOLD - 1)
                treeifyBin(tab, hash);
        }
        ++modCount;
        ++size;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key,
                              BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        Node<K,V> e; V oldValue;
        int hash = hash(key);
        if ((e = getNode(hash, key)) != null &&
            (oldValue = e.value) != null) {
            V v = remappingFunction.apply(key, oldValue);
            if (v != null) {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
            else
                removeNode(hash, key, null, false, true);
        }
        return null;
    }

    @Override
    public V compute(K key,
                     BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        V oldValue = (old == null) ? null : old.value;
        V v = remappingFunction.apply(key, oldValue);
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
        }
        else if (v != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, v);
            else {
                tab[i] = newNode(hash, key, v, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return v;
    }

    @Override
    public V merge(K key, V value,
                   BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null)
            throw new NullPointerException();
        if (remappingFunction == null)
            throw new NullPointerException();
        int hash = hash(key);
        Node<K,V>[] tab; Node<K,V> first; int n, i;
        int binCount = 0;
        TreeNode<K,V> t = null;
        Node<K,V> old = null;
        if (size > threshold || (tab = table) == null ||
            (n = tab.length) == 0)
            n = (tab = resize()).length;
        if ((first = tab[i = (n - 1) & hash]) != null) {
            if (first instanceof TreeNode)
                old = (t = (TreeNode<K,V>)first).getTreeNode(hash, key);
            else {
                Node<K,V> e = first; K k;
                do {
                    if (e.hash == hash &&
                        ((k = e.key) == key || (key != null && key.equals(k)))) {
                        old = e;
                        break;
                    }
                    ++binCount;
                } while ((e = e.next) != null);
            }
        }
        if (old != null) {
            V v;
            if (old.value != null)
                v = remappingFunction.apply(old.value, value);
            else
                v = value;
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            }
            else
                removeNode(hash, key, null, false, true);
            return v;
        }
        if (value != null) {
            if (t != null)
                t.putTreeVal(this, tab, hash, key, value);
            else {
                tab[i] = newNode(hash, key, value, first);
                if (binCount >= TREEIFY_THRESHOLD - 1)
                    treeifyBin(tab, hash);
            }
            ++modCount;
            ++size;
            afterNodeInsertion(true);
        }
        return value;
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        Node<K,V>[] tab;
        if (action == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next)
                    action.accept(e.key, e.value);
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        Node<K,V>[] tab;
        if (function == null)
            throw new NullPointerException();
        if (size > 0 && (tab = table) != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    e.value = function.apply(e.key, e.value);
                }
            }
            if (modCount != mc)
                throw new ConcurrentModificationException();
        }
    }

    /* ------------------------------------------------------------ */
    // Cloning and serialization

    /**
     * Returns a shallow copy of this <tt>HashMap</tt> instance: the keys and
     * values themselves are not cloned.
     *
     * @return a shallow copy of this map
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object clone() {
        HashMap<K,V> result;
        try {
            result = (HashMap<K,V>)super.clone();
        } catch (CloneNotSupportedException e) {
            // this shouldn't happen, since we are Cloneable
            throw new InternalError(e);
        }
        result.reinitialize();
        result.putMapEntries(this, false);
        return result;
    }

    // These methods are also used when serializing HashSets
    final float loadFactor() { return loadFactor; }
    final int capacity() {
        return (table != null) ? table.length :
            (threshold > 0) ? threshold :
            DEFAULT_INITIAL_CAPACITY;
    }

    /**
     * Save the state of the <tt>HashMap</tt> instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData The <i>capacity</i> of the HashMap (the length of the
     *             bucket array) is emitted (int), followed by the
     *             <i>size</i> (an int, the number of key-value
     *             mappings), followed by the key (Object) and value (Object)
     *             for each key-value mapping.  The key-value mappings are
     *             emitted in no particular order.
     */
    private void writeObject(java.io.ObjectOutputStream s)
        throws IOException {
        int buckets = capacity();
        // Write out the threshold, loadfactor, and any hidden stuff
        s.defaultWriteObject();
        s.writeInt(buckets);
        s.writeInt(size);
        internalWriteEntries(s);
    }

    /**
     * Reconstitute the {@code HashMap} instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(java.io.ObjectInputStream s)
        throws IOException, ClassNotFoundException {
        // Read in the threshold (ignored), loadfactor, and any hidden stuff
        s.defaultReadObject();
        reinitialize();
        if (loadFactor <= 0 || Float.isNaN(loadFactor))
            throw new InvalidObjectException("Illegal load factor: " +
                                             loadFactor);
        s.readInt();                // Read and ignore number of buckets
        int mappings = s.readInt(); // Read number of mappings (size)
        if (mappings < 0)
            throw new InvalidObjectException("Illegal mappings count: " +
                                             mappings);
        else if (mappings > 0) { // (if zero, use defaults)
            // Size the table using given load factor only if within
            // range of 0.25...4.0
            float lf = Math.min(Math.max(0.25f, loadFactor), 4.0f);
            float fc = (float)mappings / lf + 1.0f;
            int cap = ((fc < DEFAULT_INITIAL_CAPACITY) ?
                       DEFAULT_INITIAL_CAPACITY :
                       (fc >= MAXIMUM_CAPACITY) ?
                       MAXIMUM_CAPACITY :
                       tableSizeFor((int)fc));
            float ft = (float)cap * lf;
            threshold = ((cap < MAXIMUM_CAPACITY && ft < MAXIMUM_CAPACITY) ?
                         (int)ft : Integer.MAX_VALUE);
            @SuppressWarnings({"rawtypes","unchecked"})
                Node<K,V>[] tab = (Node<K,V>[])new Node[cap];
            table = tab;

            // Read the keys and values, and put the mappings in the HashMap
            for (int i = 0; i < mappings; i++) {
                @SuppressWarnings("unchecked")
                    K key = (K) s.readObject();
                @SuppressWarnings("unchecked")
                    V value = (V) s.readObject();
                putVal(hash(key), key, value, false, false);
            }
        }
    }

    /* ------------------------------------------------------------ */
    // iterators

    abstract class HashIterator {
        Node<K,V> next;        // next entry to return
        Node<K,V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            Node<K,V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {} while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K,V> nextNode() {
            Node<K,V>[] t;
            Node<K,V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {} while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            Node<K,V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class KeyIterator extends HashIterator
        implements Iterator<K> {
        public final K next() { return nextNode().key; }
    }

    final class ValueIterator extends HashIterator
        implements Iterator<V> {
        public final V next() { return nextNode().value; }
    }

    final class EntryIterator extends HashIterator
        implements Iterator<Map.Entry<K,V>> {
        public final Map.Entry<K,V> next() { return nextNode(); }
    }

    /* ------------------------------------------------------------ */
    // spliterators

    static class HashMapSpliterator<K,V> {
        final HashMap<K,V> map;
        Node<K,V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMap<K,V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                HashMap<K,V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                Node<K,V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }

    static final class KeySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<K> {
        KeySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                       int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public KeySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new KeySpliterator<>(map, lo, index = mid, est >>>= 1,
                                        expectedModCount);
        }

        public void forEachRemaining(Consumer<? super K> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.key);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super K> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        K k = current.key;
                        current = current.next;
                        action.accept(k);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    static final class ValueSpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<V> {
        ValueSpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public ValueSpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new ValueSpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super V> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p.value);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super V> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        V v = current.value;
                        current = current.next;
                        action.accept(v);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0);
        }
    }

    static final class EntrySpliterator<K,V>
        extends HashMapSpliterator<K,V>
        implements Spliterator<Map.Entry<K,V>> {
        EntrySpliterator(HashMap<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public EntrySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                new EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                                          expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K,V>> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMap<K,V> m = map;
            Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                (i = index) >= 0 && (i < (index = hi) || current != null)) {
                Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        Node<K,V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                Spliterator.DISTINCT;
        }
    }

    /* ------------------------------------------------------------ */
    // LinkedHashMap support


    /*
     * The following package-protected methods are designed to be
     * overridden by LinkedHashMap, but not by any other subclass.
     * Nearly all other internal methods are also package-protected
     * but are declared final, so can be used by LinkedHashMap, view
     * classes, and HashSet.
     */

    // Create a regular (non-tree) node
    Node<K,V> newNode(int hash, K key, V value, Node<K,V> next) {
        return new Node<>(hash, key, value, next);
    }

    // For conversion from TreeNodes to plain nodes
    // 红黑树节点转换为普通链表节点
    Node<K,V> replacementNode(Node<K,V> p, Node<K,V> next) {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    // Create a tree bin node
    TreeNode<K,V> newTreeNode(int hash, K key, V value, Node<K,V> next) {
        return new TreeNode<>(hash, key, value, next);
    }

    // For treeifyBin
    // 链表节点转换为红黑树节点
    TreeNode<K,V> replacementTreeNode(Node<K,V> p, Node<K,V> next) {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    /**
     * Reset to initial default state.  Called by clone and readObject.
     */
    void reinitialize() {
        table = null;
        entrySet = null;
        keySet = null;
        values = null;
        modCount = 0;
        threshold = 0;
        size = 0;
    }

    // Callbacks to allow LinkedHashMap post-actions
    void afterNodeAccess(Node<K,V> p) { }
    void afterNodeInsertion(boolean evict) { }
    void afterNodeRemoval(Node<K,V> p) { }

    // Called only from writeObject, to ensure compatible ordering.
    void internalWriteEntries(java.io.ObjectOutputStream s) throws IOException {
        Node<K,V>[] tab;
        if (size > 0 && (tab = table) != null) {
            for (int i = 0; i < tab.length; ++i) {
                for (Node<K,V> e = tab[i]; e != null; e = e.next) {
                    s.writeObject(e.key);
                    s.writeObject(e.value);
                }
            }
        }
    }

    /* ------------------------------------------------------------ */
    // Tree bins

    /**
     * Entry for Tree bins. Extends LinkedHashMap.Entry (which in turn
     * extends Node) so can be used as extension of either regular or
     * linked node.
     */
    static final class TreeNode<K,V> extends LinkedHashMap.Entry<K,V> {
        TreeNode<K,V> parent;  // red-black tree links
        TreeNode<K,V> left;
        TreeNode<K,V> right;
        TreeNode<K,V> prev;    // needed to unlink next upon deletion
        boolean red;
        TreeNode(int hash, K key, V val, Node<K,V> next) {
            super(hash, key, val, next);
        }

        /**
         * Returns root of tree containing this node.
         */
        final TreeNode<K,V> root() {
            for (TreeNode<K,V> r = this, p;;) {
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }

        /**
         * Ensures that the given root is the first node of its bin.
         * 把红黑树的根节点放到table数组的对应位置(之前数组上放的可能不是根节点)
         */
        static <K,V> void moveRootToFront(Node<K,V>[] tab, TreeNode<K,V> root) {
            // n代表table数组的长度
            int n;
            // 数组长度大于0并且有root节点才进行后面的操作
            if (root != null && tab != null && (n = tab.length) > 0) {
                // index代表根节点应该放在table数组的下标
                int index = (n - 1) & root.hash;
                // first代表当前数组下标处存放的节点
                TreeNode<K,V> first = (TreeNode<K,V>)tab[index];
                // 如果两个节点不是同一个才进行调整，一样的话就不用调整了
                // 调整方法就是把root节点从双向链表中独立出来放到数组中的正确位置作为链表头，独立就需要改变之前的前驱
                // 节点指针和后继节点指针，把前驱节点和后继节点连在一起，再把root的前驱节点指针置为null(root已经成为头
                // 结点了)，后继节点指向之前的头结点，之前的头结点的前驱指向root，保证链表的完整性。
                if (root != first) {
                    // rn代表root节点在双向链表的后继节点
                    Node<K,V> rn;
                    // 先把root节点直接放到正确的位置
                    tab[index] = root;
                    // rp代表root节点在双向链表中的前驱节点
                    TreeNode<K,V> rp = root.prev;
                    // root节点有后继节点就把后继节点的前驱节点指针指向root的前驱节点(略过root节点)
                    if ((rn = root.next) != null)
                        ((TreeNode<K,V>)rn).prev = rp;
                    // root节点有前驱节点就把前驱节点的后继节点指针指向root的后继节点(略过root节点)
                    if (rp != null)
                        rp.next = rn;
                    // 经过上面两个操作root节点已经从链表中独立出来了，接下来就需要用root节点代替头结点
                    if (first != null)
                        // 原来的头结点的前驱指向root节点，这样first就不再是头结点了
                        first.prev = root;
                    // root的后继节点指向之前的头结点
                    root.next = first;
                    // root节点成为头结点后也就没有前驱节点了
                    root.prev = null;
                }
                // 验证红黑树的结构是否正确
                assert checkInvariants(root);
            }
        }

        /**
         * Finds the node starting at root p with the given hash and key.
         * The kc argument caches comparableClassFor(key) upon first use
         * comparing keys.
         */
        final TreeNode<K,V> find(int h, Object k, Class<?> kc) {
            TreeNode<K,V> p = this;
            do {
                // ph表示当前p节点的hash
                // dir表示当hash相等但是key不等时k和p.key比较出来的大小关系
                // pk表示当前p节点的key
                int ph, dir; K pk;
                // pl为p的左孩子
                // pr为p的右孩子
                // q为在子树中找到的和k相等的节点
                TreeNode<K,V> pl = p.left, pr = p.right, q;
                if ((ph = p.hash) > h)
                    // h小于当前节点hash,就在左子树继续查找，左子树为null则返回null表示未找到
                    p = pl;
                else if (ph < h)
                    // h大于当前节点hash,就在右子树继续查找，右子树为null则返回null表示未找到
                    p = pr;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    // hash相等并且key也相等则表示找到了，返回当前节点p
                    return p;
                else if (pl == null)
                    // hash相等并且key不等并且没有左子树，那就继续在右子树查找，右子树为null则返回null表示未找到
                    p = pr;
                else if (pr == null)
                    // hash相等并且key不等并且没有右子树，那就继续在左子树查找，左子树为null则返回null表示未找到
                    p = pl;
                // hash相等、key不相等、左右子树都存在，key能够通过Comparable比较大小则比较key的大小
                else if ((kc != null ||
                          (kc = comparableClassFor(k)) != null) &&
                         (dir = compareComparables(kc, k, pk)) != 0)
                    // k小于pk则在左子树找，大于在右子树找，等于就在右子树递归查找
                    p = (dir < 0) ? pl : pr;
                // hash相等、key不相等、左右子树都存在，key不能够通过Comparable比较出大小则在右子树进行递归查找
                else if ((q = pr.find(h, k, kc)) != null)
                    return q;
                else
                    // 右子树递归查找不到就在左子树查找
                    p = pl;
            } while (p != null);
            // 查找到叶子节点都没找到就返回null
            return null;
        }

        /**
         * Calls find for root node.
         * 从红黑树的根节点开始查找
         */
        final TreeNode<K,V> getTreeNode(int h, Object k) {
            // 自己是根节点就从自己开始查找，否则拿到根节点再开始查找
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /**
         * Tie-breaking utility for ordering insertions when equal
         * hashCodes and non-comparable. We don't require a total
         * order, just a consistent insertion rule to maintain
         * equivalence across rebalancings. Tie-breaking further than
         * necessary simplifies testing a bit.
         */
        static int tieBreakOrder(Object a, Object b) {
            int d;
            // 如果a和b的类名可以比较出大小就返回类名比较出来的大小(类名是字符串可以比较)
            if (a == null || b == null ||
                (d = a.getClass().getName().
                 compareTo(b.getClass().getName())) == 0)
                // 否则类名一样的就直接使用对象的hashCode()函数生成的hash来比较
                // 小于等于都算小于
                // 大于就算大于
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ?
                     -1 : 1);
            return d;
        }

        /**
         * Forms tree of the nodes linked from this node.
         * 把双向链表串起来的红黑树节点构造成一棵红黑树
         * @return root of tree
         */
        final void treeify(Node<K,V>[] tab) {
            // root代表红黑树的根节点
            TreeNode<K,V> root = null;
            // x初始化为当前红黑树节点，也就是链表的头结点
            // x代表遍历链表过程中的当前遍历节点
            for (TreeNode<K,V> x = this, next; x != null; x = next) {
                // 遍历下一个节点(这句放在循环结尾更好理解)
                next = (TreeNode<K,V>)x.next;
                // 当前遍历节点的左右子树指针都置为null
                x.left = x.right = null;
                // 如果是第一遍循环，那么设置第一个节点为根节点
                if (root == null) {
                    // 根节点父亲节点为null
                    x.parent = null;
                    // 红黑树根节点为黑色
                    x.red = false;
                    // 根节点指向当前遍历节点
                    root = x;
                }
                else {
                    // k代表当前遍历节点的key
                    K k = x.key;
                    // h代表当前遍历节点的hash
                    int h = x.hash;
                    // kc代表当前遍历节点的key实现了Comparable的类，没有实现Comparable就是null
                    Class<?> kc = null;
                    // 把当前遍历节点放到红黑树中，需要从根节点开始查找要放的位置
                    // p代表查找红黑树过程中正在查找的节点
                    for (TreeNode<K,V> p = root;;) {
                        // dir代表当前待插入节点和红黑树中节点hash的大小关系，小于红黑树中节点为-1，大于为1
                        // ph代表当前红黑树节点的hash
                        int dir, ph;
                        // pk代表当前红黑树节点的key
                        K pk = p.key;
                        // 判断大小，这里有3种情况
                        // 1.插入节点的hash小于当前判断红黑树节点的hash
                        // 2.插入节点的hash大于当前判断红黑树节点的hash
                        // 2.插入节点的hash等于当前判断红黑树节点的hash
                        if ((ph = p.hash) > h)
                            // 小于时dir为-1
                            dir = -1;
                        else if (ph < h)
                            // 大于时dir为1
                            dir = 1;
                        // 等于时如果key实现了Comparable接口就使用比较出来的结果为dir的值
                        // 如果没有实现Comparable接口或者比较的结果为相等那么久最终PK
                        else if ((kc == null &&
                                  (kc = comparableClassFor(k)) == null) ||
                                 (dir = compareComparables(kc, k, pk)) == 0)
                            // 最终PK比较类名或者hashCode()
                            dir = tieBreakOrder(k, pk);

                        // xp临时保存当前查找的红黑树节点
                        TreeNode<K,V> xp = p;
                        // 插入节点hash小于等于当前判断红黑树节点就继续在左子树查找
                        // 大于当前节点就在右子树查找
                        // 直到左子树或者右子树为null的时候，就找到了待插入节点要插入的位置
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            // 待插入节点的父亲节点为临时保存的当前遍历的红黑树节点
                            x.parent = xp;
                            // 把插入的节点挂到父亲节点上
                            if (dir <= 0)
                                // 小于等于挂左子树
                                xp.left = x;
                            else
                                // 大于挂右子树
                                xp.right = x;
                            // 红黑树每次插入节点需要进行平衡操作，保证符合红黑树的五大性质
                            root = balanceInsertion(root, x);
                            // 平衡结束后进行下一个节点的插入
                            break;
                        }
                    }
                }
            }
            // 所有节点都放到红黑树上了就把红黑树的根节点放到数组上(经过多次平衡操作后之前的链表头结点不一定就是根节点)
            moveRootToFront(tab, root);
        }

        /**
         * Returns a list of non-TreeNodes replacing those linked from
         * this node.
         * 将红黑树节点链表转换为普通节点链表(改变节点类型，双向链表变为单向链表)
         */
        final Node<K,V> untreeify(HashMap<K,V> map) {
            // hd代表新链表头结点
            // tl代表新链表尾节点
            Node<K,V> hd = null, tl = null;
            // 遍历红黑树节点链表
            for (Node<K,V> q = this; q != null; q = q.next) {
                // 转换单个节点，把尾指针置null
                Node<K,V> p = map.replacementNode(q, null);
                // 没有尾节点当前节点就是头结点
                if (tl == null)
                    hd = p;
                else
                    // 链表尾指针指向当前节点
                    tl.next = p;
                // 当前节点成为尾节点
                tl = p;
            }
            // 返回头结点
            return hd;
        }

        /**
         * Tree version of putVal.
         * 该函数作用是在红黑树中找是否有和待添加key相同的key已经存在，有则返回存在的节点，没有则新建一个节点插入红黑树中并返回null
         *
         * map 当前节点所在的HashMap对象
         * tab 当前HashMap对象的元素数组
         * h   指定key的hash值
         * k   指定key
         * v   指定key上要写入的值
         * 返回：指定key所匹配到的节点对象，针对这个对象去修改V(返回nul说明创建了一个新节点)
         */
        final TreeNode<K,V> putTreeVal(HashMap<K,V> map, Node<K,V>[] tab,
                                       int h, K k, V v) {
            // key的class对象
            Class<?> kc = null;
            // 是否在红黑树上搜索过和key相等的节点，未必是从根节点遍历的，但是遍历路径上一定已经包含了后续需要比对的所有节点。
            boolean searched = false;
            // 当前节点有父节点就获取当前红黑树的root节点赋值给root，没有父节点则说明自己就是root节点
            TreeNode<K,V> root = (parent != null) ? root() : this;
            // 初始化p为根节点，然后在红黑树上查找key应该插入的位置
            for (TreeNode<K,V> p = root;;) {
                // dir代表插入节点的hash和当前p节点hash的大小关系
                // ph代表p节点的hash
                // pk代表p节点的key
                int dir, ph; K pk;
                // 如果插入节点hash小于p节点hash则dir为-1
                if ((ph = p.hash) > h)
                    dir = -1;
                // 如果插入节点hash大于p节点hash则dir为1
                else if (ph < h)
                    dir = 1;
                // 如果两个hash相等并且key也相等则表示找到了相同的节点，直接返回，在外层方法会对v进行写入
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                // 如果两个hash相等但是key不相等就在树上查找是否有hash相等并且equals也相等的节点

                // 第一次循环时kc必定是null，就会看key是否实现了comparable接口
                // 1.如果实现了comparable接口则会使用compareTo比较两个key的大小，比较结果如果是相等逻辑上说不通(equals不相等compareTo相等)
                // 则进入if语句块在红黑树上查找是否有相等的，没有找到后面循环不会再进入此语句块，为什么不进行comparable比较或者最终PK？？？ //FIXME
                // 2.如果没有实现comparable接口则直接进入if语句块，没有找到的话后面的循环都会进入语句块进行最终PK
                else if ((kc == null &&
                        // 判断key是否实现了comparable接口，未实现kc为null
                          (kc = comparableClassFor(k)) == null) ||
                        // key实现了comparable接口的情况下比较当前节点的k和插入节点key的大小，结果赋值给dir
                         (dir = compareComparables(kc, k, pk)) == 0) {
                    // 代码执行到这里说明插入的key没有实现comparable接口或者实现了comparable接口但是和当前节点的键对象比较之后相等

                    // 因为是在树种进行搜索，如果搜索过肯定就有结果了
                    // 如果第一次找到了节点则函数已经返回，既然还能走到这里说明在树中没有找到节点，也不用找了
                    if (!searched) {
                        // q表示找到的和key相等的节点
                        // ch表示当前p节点的子树节点
                        TreeNode<K,V> q, ch;
                        searched = true;
                        // 在红黑树中查找，短路查找，左子树中找到后就不用在右子树中再进行查找，find()方法里面会递归查找
                        if (((ch = p.left) != null &&
                             (q = ch.find(h, k, kc)) != null) ||
                            ((ch = p.right) != null &&
                             (q = ch.find(h, k, kc)) != null))
                            // 找到了和插入key的hash和key都相等的节点就返回
                            return q;
                    }
                    // 红黑树中没有找到和key相等的节点，需要进行插入操作，所以进行最终PK，使用hashcode()方法生成的
                    // hashcode比较出大小用于区分插入左子树还是右子树
                    dir = tieBreakOrder(k, pk);
                }

                // 当前节点保存在xp变量上
                TreeNode<K,V> xp = p;
                // 如果dir小于等于0，那么看当前节点的左节点是否为空，如果为空，就可以把要添加的元素作为当前节点的左节点，如果不为空，还需要下一轮继续比较
                // 如果dir大于0，那么看当前节点的右节点是否为空，如果为空，就可以把要添加的元素作为当前节点的右节点，如果不为空，还需要下一轮继续比较
                // 如果以上两条当中有一个子节点不为空，这个if中还做了一件事，那就是把p已经指向了对应的不为空的子节点，开始下一轮的比较
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    // 保存p节点的下一个节点
                    Node<K,V> xpn = xp.next;
                    // 新建一个红黑树节点，把next指向父节点的next节点
                    TreeNode<K,V> x = map.newTreeNode(h, k, v, xpn);
                    if (dir <= 0)
                        // 如果hash小于等于p节点的hash就放在p节点的左孩子，之前的左孩子为null
                        xp.left = x;
                    else
                        // 如果hash大于p节点的hash就放在p节点的右孩子，之前的有孩子为null
                        xp.right = x;
                    // p的next指向新节点(也就是把新节点插入到了p节点的后面)
                    xp.next = x;
                    // 新节点的父节点和前驱节点都指向p
                    x.parent = x.prev = xp;
                    // 如果p节点之前的next不是null，现在把新节点插入p后面就还要把之前的next的前驱节点指向新节点，维护双向链表关系
                    if (xpn != null)
                        ((TreeNode<K,V>)xpn).prev = x;
                    // 插入节点后对红黑树进行平衡操作
                    // 把红黑树的根节点放到table数组上
                    moveRootToFront(tab, balanceInsertion(root, x));
                    // 返回null表示在红黑树中没有找到和待插入key相等的节点，有新节点插入
                    return null;
                }
            }
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         * 红黑树删除操作
         */
        final void removeTreeNode(HashMap<K,V> map, Node<K,V>[] tab,
                                  boolean movable) {
            int n;
            if (tab == null || (n = tab.length) == 0)
                return;
            int index = (n - 1) & hash;
            TreeNode<K,V> first = (TreeNode<K,V>)tab[index], root = first, rl;
            TreeNode<K,V> succ = (TreeNode<K,V>)next, pred = prev;
            if (pred == null)
                tab[index] = first = succ;
            else
                pred.next = succ;
            if (succ != null)
                succ.prev = pred;
            if (first == null)
                return;
            if (root.parent != null)
                root = root.root();
            if (root == null || root.right == null ||
                (rl = root.left) == null || rl.left == null) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            TreeNode<K,V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null) {
                TreeNode<K,V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red; s.red = p.red; p.red = c; // swap colors
                TreeNode<K,V> sr = s.right;
                TreeNode<K,V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else {
                    TreeNode<K,V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p) {
                TreeNode<K,V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            TreeNode<K,V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p) {  // detach
                TreeNode<K,V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        /**
         * Splits nodes in a tree bin into lower and upper tree bins,
         * or untreeifies if now too small. Called only from resize;
         * see above discussion about split bits and indices.
         * 将红黑树拆分放到新的数组上，拆分后每棵树节点数如果小于树化恢复阈值就恢复成链表形态
         *
         * @param map the map
         * @param tab the table for recording bin heads
         * @param index the index of the table being split
         * @param bit the bit of hash to split on
         */
        final void split(HashMap<K,V> map, Node<K,V>[] tab, int index, int bit) {
            // b代表原来的红黑树根节点
            TreeNode<K,V> b = this;
            // Relink into lo and hi lists, preserving order
            // 数组扩容后原来红黑树要拆成两部分
            // loHead和loTail分别代表位置不变的节点链表头尾节点
            // hoHead和hoTail分别代表位置改变的节点链表头尾节点
            TreeNode<K,V> loHead = null, loTail = null;
            TreeNode<K,V> hiHead = null, hiTail = null;
            // lc代表位置不变节点数
            // hc代表位置改变节点数
            int lc = 0, hc = 0;
            // 通过红黑树的链表指针遍历红黑树所有节点
            for (TreeNode<K,V> e = b, next; e != null; e = next) {
                // 下一轮迭代
                next = (TreeNode<K,V>)e.next;
                // 去掉后继节点指针(虽然在组成链表时重新指定了尾节点的后继节点，但是会导致最后一个遍历
                // 的节点next指针没有重新指定，因此直接在开始去掉后继指针)
                e.next = null;
                // 判断是在原位置还是在原位置+原数组大小位置，拆分成两个红黑树链表(拆分过后树结构被破坏)
                if ((e.hash & bit) == 0) {
                    // 将当前遍历节点e的前驱节点指向链表尾，如果链表尾是null则表示e是第一个节点
                    if ((e.prev = loTail) == null)
                        // e是第一个节点，链表头指向e
                        loHead = e;
                    else
                        // 有链表尾的情况把链表尾的后继节点指向当前节点e
                        loTail.next = e;
                    // 链表尾指向e
                    loTail = e;
                    ++lc;
                }
                else {
                    // 一样的逻辑，组成新的双向链表
                    if ((e.prev = hiTail) == null)
                        hiHead = e;
                    else
                        hiTail.next = e;
                    hiTail = e;
                    ++hc;
                }
            }

            // 如果原位置处还有节点
            if (loHead != null) {
                // 节点个数小于等于树化恢复阈值就将红黑树节点链表转换为普通节点链表，
                // 否则将红黑树节点链表重新组成新的红黑树
                if (lc <= UNTREEIFY_THRESHOLD)
                    // 把链表中每个红黑树节点转换为普通节点并将头结点放入新数组原下标位置
                    tab[index] = loHead.untreeify(map);
                else {
                    // 头结点放入新数组原下表位置
                    tab[index] = loHead;
                    // 另一个位置处如果有节点才进行树化操作(此时的链表中虽然是红黑树节点，但是树结构已经不存在了，
                    // 如果另一个位置没有节点的话说明当前链表中就是拆分前的所有数据，本身就是红黑树，不需要树化)
                    if (hiHead != null) // (else is already treeified)
                        loHead.treeify(tab);
                }
            }
            // 如果原位置+元素组大小处还有节点，操作同上，只是放入新数组的下标变成了原下标+原数组大小
            if (hiHead != null) {
                if (hc <= UNTREEIFY_THRESHOLD)
                    tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead;
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }

        /* ------------------------------------------------------------ */
        // Red-black tree methods, all adapted from CLR

        static <K,V> TreeNode<K,V> rotateLeft(TreeNode<K,V> root,
                                              TreeNode<K,V> p) {
            TreeNode<K,V> r, pp, rl;
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K,V> TreeNode<K,V> rotateRight(TreeNode<K,V> root,
                                               TreeNode<K,V> p) {
            TreeNode<K,V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        /**
         * 插入操作后对红黑树进行平衡操作
         *
         * @param root 根节点
         * @param x 插入的节点
         * @return java.util.HashMap.TreeNode<K, V>
         */
        static <K,V> TreeNode<K,V> balanceInsertion(TreeNode<K,V> root,
                                                    TreeNode<K,V> x) {
            // 新插入的节点默认为红色
            x.red = true;
            // xp代表当前节点的父亲节点
            // xpp代表当前节点的爷爷节点
            // xppl代表当前节点的爷爷的左孩子(左叔叔)
            // xppr代表当前节点的爷爷的右孩子(右叔叔)
            for (TreeNode<K,V> xp, xpp, xppl, xppr;;) {
                // 1.插入节点就是根节点
                if ((xp = x.parent) == null) {
                    // 根节点颜色变黑
                    x.red = false;
                    // 不用其他操作
                    return x;
                }
                // 2.插入节点父亲节点是黑色(对应234树的1节点，插入后变成2节点，上黑下红) (父亲节点是红色，爷爷节点不存在的情况应该是不存在)
                //      (A)黑
                //      /
                //    (B)红
                else if (!xp.red || (xpp = xp.parent) == null)
                    // 父亲是黑色插入节点是红色，不影响红黑树的平衡性，不用操作
                    return root;
                // 3.父亲节点是红色这里分两种情况，会了一种另一种反着调整就可以了
                // 1.父亲节点是爷爷的左孩子
                // 2.父亲节点是爷爷的右孩子
                if (xp == (xppl = xpp.left)) {
                    // 3.1存在右叔叔节点并且右叔叔节点为红色(对应在234树的3节点插入，中间黑两边红)
                    // 这时插入一个红节点导致和父亲的红节点连续了，需要把父亲和叔叔变为黑色，爷爷变成红色，
                    // 爷爷变成红色后就要把爷爷当成新插入的红色节点继续向上进行平衡
                    //                  (A)黑                            (A)红
                    //                  /    \                          /     \
                    //                (B)红  (C)红    ->              (B)黑   (C)黑
                    //                /                               /
                    //              (C)新                           (C)新
                    if ((xppr = xpp.right) != null && xppr.red) {
                        // 叔叔变黑
                        xppr.red = false;
                        // 父亲变黑
                        xp.red = false;
                        // 爷爷变红
                        xpp.red = true;
                        // 继续处理红色爷爷节点
                        x = xpp;
                    }
                    // 3.2不存在右叔叔或者右叔叔是黑色(nul节点)(其实就在在234树的2节点插入一个新的节点，需要把父亲变黑，爷爷变红，并且旋转)
                    else {
                        // 先要保证插入节点和父亲、爷爷在一个方向，不然就要先旋转到一个方向
                        //          (A)黑                            (A)黑
                        //          /                                /
                        //        (B)红          ->                (C)红
                        //          \                              /
                        //            (C)新                      (B)新
                        if (x == xp.right) {
                            // x是父亲的右节点就要旋转成左节点，以父亲为轴进行左旋，同时x指向父亲
                            root = rotateLeft(root, x = xp);
                            // 旋转过后关系都要变化，父亲和爷爷都需要重新获取
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        //      (A)黑               (B)黑
                        //    /                     /   \
                        //   (B)红      ->      (C)红    (A)红
                        //  /
                        // (C)新
                        // 父亲节点是红色，爷爷节点是黑色，就把父亲变黑，爷爷变红，以爷爷为轴进行右旋
                        // 爷爷就成了兄弟
                        if (xp != null) {
                            // 父亲变黑
                            xp.red = false;
                            if (xpp != null) {
                                // 爷爷变红
                                xpp.red = true;
                                // 以爷爷为轴右旋
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                }
                // 跟上面一样，方向相反
                else {
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        static <K,V> TreeNode<K,V> balanceDeletion(TreeNode<K,V> root,
                                                   TreeNode<K,V> x) {
            for (TreeNode<K,V> xp, xpl, xpr;;)  {
                if (x == null || x == root)
                    return root;
                else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (x.red) {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                            (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }
                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                    null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else {
                        TreeNode<K,V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                            (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        }
                        else {
                            if (sl == null || !sl.red) {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                    null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * Recursive invariant check
         * 验证红黑树的结构是否正确
         * 这一步是防御性的编程
         * 校验TreeNode对象是否满足红黑树和双链表的特性
         * 如果这个方法校验不通过：可能是因为用户编程失误，破坏了结构(例如：并发场景下)
         * 也可能是TreeNode的实现有问题(这个是理论上的以防万一)
         */
        static <K,V> boolean checkInvariants(TreeNode<K,V> t) {
            TreeNode<K,V> tp = t.parent, tl = t.left, tr = t.right,
                tb = t.prev, tn = (TreeNode<K,V>)t.next;
            if (tb != null && tb.next != t)
                return false;
            if (tn != null && tn.prev != t)
                return false;
            if (tp != null && t != tp.left && t != tp.right)
                return false;
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            if (tl != null && !checkInvariants(tl))
                return false;
            if (tr != null && !checkInvariants(tr))
                return false;
            return true;
        }
    }

}
