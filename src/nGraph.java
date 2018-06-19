import java.util.ArrayList;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Vector;
import java.util.List;


public class nGraph {
    private int noV;
    List<List<Double>> w;
    List<List<Boolean>> link;
    //Vector<Vector<Double>> cap;
    Vector<Double> cap;
    private ArrayList<Boolean> node;
    
    //random
    public nGraph(int V)
    {
    	this.noV =V;
   	 	this.cap = new Vector<Double>();
   	 	this.w= new ArrayList<List<Double>>();
   	 	this.link = new ArrayList<List<Boolean>>();
   	 	this.node = new ArrayList<Boolean>();
	   	 for (int i=0;i<V;i++)
	   	 {
	   		 ArrayList<Double> temp1 = new ArrayList<>();   
	   		ArrayList<Boolean> temp2= new ArrayList<>();;
	   		 for (int j=0;j<V;j++)
	   		 {
	   			 temp1.add(0.0);
	   			 temp2.add(false);
	   		 } 
	   		this.w.add(temp1);	
	   		this.link.add(temp2);
	   	 }
	   	for (int i=0;i<V;i++)
        {
      	  this.cap.add(0.0);
      	  this.node.add(false);
        }    
	   	 
    }
    public nGraph(int V,Vector<Double> dataReal )
    {
    	this.noV =V;
    	 this.cap = new Vector<Double>();
    	this.w= new ArrayList<List<Double>>();
    	this.link = new ArrayList<List<Boolean>>();
    	this.node = new ArrayList<Boolean>();
    	for (int i=0;i<V;i++)
    	{
    		ArrayList<Double> temp1 = new ArrayList<>();    		
    		for(int j=0;j<i;j++)
    		{
    			temp1.add(w.get(j).get(i));
    		}
    		temp1.add(0.0);	
    		for(int j=i+1;j<V;j++)
    		{
    			double b= UtilizeFunction.randomDouble(new Integer[] {0,0,0,10000,10000,10000,10000});
    			temp1.add(b);
    			
    		}
    		this.w.add(i, temp1);
    	}
    	for(int i=0;i<V;i++)
    	{
    		ArrayList<Boolean> temp2= new ArrayList<>();;
        	for (int j=0;j<V;j++)
        	{
        		if(w.get(i).get(j)!=0)
        			temp2.add(true);
        		else
        			temp2.add(false);
        	} 
        	this.link.add(temp2);
    	}
        for (int i=0;i<V;i++)
        {
      	  this.cap.add(dataReal.get(i));
      	  this.node = new ArrayList<>();
      	  if(dataReal.get(i)>0)
      		  this.node.add(true);
      	  else
      		  this.node.add(false);
        }    	
    	
    }
    public nGraph(Vector<Double> K, List<List<Double>> w) 
    {//model newest
    this.noV = K.size();      
	  this.w= new ArrayList<List<Double>>();
	  this.cap = new Vector<Double>(noV);
	  //this.Nprice = new Vector<Vector<Double>>(V);
	  this.node = new ArrayList<Boolean>();
	  this.link = new ArrayList<List<Boolean>>();
	  for (int i=0;i<noV;i++)
      {
      	ArrayList<Boolean> temp1=new ArrayList<>();
      	for (int j=0;j<noV;j++)
      	{
      		temp1.add(false);
      	}
      	this.link.add(temp1);
      }
     for (int i=0;i<w.size();i++)
     {
    	ArrayList<Double> temp= new ArrayList<>();
     	for (int j=0;j<w.get(0).size();j++)
     	{
     		temp.add(w.get(i).get(j));
     		if(w.get(i).get(j)>0)
     			this.link.get(i).set(j, true);
     	}
     	this.w.add(temp);
     }
     for (int i=0;i<noV;i++)
     {
   	  this.cap.addElement(K.get(i));
   	  if(K.get(i)>0)
		  this.node.add(true);
	  else
		  this.node.add(false);
     }
         
  }
    
    public int addVertex(double t)//tra ve so dinh cua do thi
    {
    	this.noV = this.noV+1;
    	this.cap.add(t);
    	ArrayList<Boolean> temp1=new ArrayList<>();
        	for (int j=0;j<noV;j++)
        	{
        		temp1.add(false);
        	}
        	this.link.add(temp1);
      	ArrayList<Double> temp= new ArrayList<>();
       	for (int j=0;j<noV;j++)
       	{
       		temp.add(0.0);
       	}
       	this.w.add(temp);
    	return this.noV;
    }
    
    // number of vertices and edges
    public int getV(){ return noV; }
    public double getCap(int v)//new model
    {
    	return cap.get(v-1);
    }
    public boolean setCap(int v, double c)//new model
    {
    	cap.set(v-1, c);
    	if(c>0)
    		node.set(v-1, true);
    	return true;
    }
    public boolean addCap(int v, double c)//new model
    {
    	cap.set(v-1,c+cap.get(v-1));
    	if(c>0)
    		node.set(v-1, true);
    	return true;
    }
    public boolean minusCap(int v,double c)//new model
    {
    	cap.set(v-1,cap.get(v-1)-c);
    	if(cap.get(v-1)>0)
    	{
    		this.node.set(v-1, true);
    	}
    	return true;
    }
    public boolean setEdgeWeight(int v, int u,double c)
    {   	
    	if(c>0)
    	{
    		this.w.get(v-1).set(u-1, c);
    		this.link.get(v-1).set(u-1, true);
    	}
    	else
    	{
    		this.w.get(v-1).set(u-1, 0.0);
    		this.link.get(v-1).set(u-1, false);
    	}
    	return true;
    }
    public boolean addEdgeWeight(int v, int u,double c)
    {
    	double t1 =this.w.get(v-1).get(u-1);
    	this.w.get(v-1).set(u-1, t1+c);
    	this.link.get(v-1).set(u-1, true);
    	return true;
    }
    public double getEdgeWeight(int u, int v)
    {
    		return this.w.get(u-1).get(v-1);
    }
    public boolean getExistNode(int u)
    {
    	return this.node.get(u-1);
    } 
    public boolean getExistLink(int u, int v)
    {
    	return this.link.get(u-1).get(v-1);
    }
    
    public void removeNode(int u)
    {
    	//danh dau dinh khong duoc xet
    	
    	this.node.set(u-1, false);
    }
    public void removeLink(int u,int v)
    {
    	//danh dau dinh khong duoc xet0
    	this.w.get(u-1).set(v-1, 0.0);
    	this.link.get(u-1).set(v-1, false);
    }

    // does the graph contain the edge v-w?
    public boolean contains(int u, int v) {
        return (w.get(u-1).get(v-1)>0);
    }

    // return list of neighbors of v
    public Iterable<Integer> link_bandwidth(int v) {
        return new AdjIterator(v-1);
    }
    // support iteration over graph vertices
    private class AdjIterator implements Iterator<Integer>, Iterable<Integer> {
        int u, v = 0;
        AdjIterator(int u) { this.u = u; }

        public Iterator<Integer> iterator() { return this; }

        public boolean hasNext() {
            while (v < noV) {
                if (w.get(u).get(v)>0) return true;
                v++;
            }
            return false;
        }

        public Integer next() {
            if (hasNext()) { return v++;                         }
            else           { throw new NoSuchElementException(); }
        }

        public void remove()  { throw new UnsupportedOperationException();  }
    }

    // test client
    public static void main(String[] args) {
        
    }

}