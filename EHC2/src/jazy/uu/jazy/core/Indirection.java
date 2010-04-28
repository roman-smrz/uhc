package uu.jazy.core ;/** * Lazy and Functional. * Package for laziness and functions as known from functional languages. * Written by Atze Dijkstra, atze@cs.uu.nl * * $Header:     $ * $Archive:    $ * $NoKeywords: $ */import java.util.* ;import java.io.* ;/** * Indirection. * To be used in 'letrec' situations. * Java does not allow for forward references to variables, i.e. use before declare. * With an Indirection one first declares the indirection, uses it and later sets * with the then known value. * Typical usage:    <pre>        Indirection v_ind = new Indirection() ;        Object v = ... v_ind ... ;        v_ind.set( v ) ;    </pre> */public class Indirection extends Apply0{    public Indirection()    {        super( null ) ;    }        protected void evalSet()    {        if ( funcOrVal != null )            funcOrVal = funcOrVal ;        else            funcOrVal = null ;//StdVals.nil ; //StdFuncs.error( "eval of Indirection before setting it" ) ;    }        public void set( Object fv )    {        funcOrVal = fv ;    }}