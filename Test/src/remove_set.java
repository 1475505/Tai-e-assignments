package src;

import java.util.HashSet;
import java.util.Set;

/**
 * @author ll （ created: 2022-09-17 14:07 )
 */
public class remove_set {
    public static void main(String[] args){
        var a = new HashSet<Integer>();
        a.add(1);
        a.add(2);
        var b = a.remove(1);
        System.out.println(a);
    }
}
