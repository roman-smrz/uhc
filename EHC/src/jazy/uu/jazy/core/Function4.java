package uu.jazy.core ;

/**
 * Lazy and Functional.
 * Package for laziness and functions as known from functional languages.
 * Written by Atze Dijkstra, atze@cs.uu.nl
 */

import java.util.* ;
import java.io.* ;

/**
 * Function accepting/expecting 4 parameter(s).
 * @see uu.jazy.core.Function
 */
public abstract class Function4 extends Function
{
    public Function4( )
    {
        nrParams = 4 ;
    }
    
    public Function4( String nm )
    {
        this() ;
        setName ( nm ) ;
    }
    
    public Function4( Function prev, String nm )
    {
        this( prev.getName() + "." + nm ) ;
    }
        
    abstract protected Object eval4( Object v1, Object v2, Object v3, Object v4 ) ;

    public Apply apply1( Object v1 )
    {
        return new Apply1F4( this, v1 ) ;
    }
    
    public Apply apply2( Object v1, Object v2 )
    {
        return new Apply2F4( this, v1, v2 ) ;
    }
    
    public Apply apply3( Object v1, Object v2, Object v3 )
    {
        return new Apply3F4( this, v1, v2, v3 ) ;
    }
    
    public Apply apply4( Object v1, Object v2, Object v3, Object v4 )
    {
        return new Apply4F4( this, v1, v2, v3, v4 ) ;
    }
    
    public Apply apply5( Object v1, Object v2, Object v3, Object v4, Object v5 )
    {
        return apply4( v1, v2, v3, v4 ).apply1( v5 ) ;
    }
    
}

class Apply1F4 extends Apply1
{
	public Apply1F4( Object f, Object p1 )
	{
		super( f, p1 ) ;
		nrNeededParams = 3 ;
	}
	
    public Apply apply1( Object v1 )
    {
        return new Apply2F4( funcOrVal, p1, v1) ;
        //return new Apply1A1F4( this, v1) ;
    }
    
    public Apply apply2( Object v1, Object v2 )
    {
        return new Apply3F4( funcOrVal, p1, v1, v2) ;
        //return new Apply2A1F4( this, v1, v2) ;
    }
    
    public Apply apply3( Object v1, Object v2, Object v3 )
    {
        return new Apply4F4( funcOrVal, p1, v1, v2, v3) ;
    }
    
}

class Apply2F4 extends Apply2
{
	public Apply2F4( Object f, Object p1, Object p2 )
	{
		super( f, p1, p2 ) ;
		nrNeededParams = 2 ;
	}
	    
    public Apply apply1( Object v1 )
    {
        return new Apply3F4( funcOrVal, p1, p2, v1 ) ;
    }
    
    public Apply apply2( Object v1, Object v2 )
    {
        return new Apply4F4( funcOrVal, p1, p2, v1, v2) ;
    }
    
}

class Apply3F4 extends Apply3
{
	public Apply3F4( Object f, Object p1, Object p2, Object p3 )
	{
		super( f, p1, p2, p3 ) ;
		nrNeededParams = 1 ;
	}
	
    public Apply apply1( Object v1 )
    {
        return new Apply4F4( funcOrVal, p1, p2, p3, v1 ) ;
    }
    
}

class Apply4F4 extends Apply4
{
	public Apply4F4( Object f, Object p1, Object p2, Object p3, Object p4 )
	{
		super( f, p1, p2, p3, p4 ) ;
	}
	
    protected void evalSet(  )
    {
        funcOrVal = ((Function4)funcOrVal).eval4( p1, p2, p3, p4 ) ;
        p1 = p2 = p3 = p4 = null ;
    }
    
}

