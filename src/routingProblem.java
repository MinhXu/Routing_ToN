import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
//import java.util.ListIterator;
import java.util.Vector;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.math.BigDecimal;
import java.util.*;

import org.apache.commons.io.FileUtils;
//import org.apache.commons.collections15.Transformer;
//import gurobi.*;
import org.uncommons.maths.random.*;
import org.jgrapht.DirectedGraph;
import org.jgrapht.GraphPath;
import org.jgrapht.VertexFactory;
import org.jgrapht.alg.*;
import org.jgrapht.graph.*;
import org.jgrapht.generate.*;


public class routingProblem {
	static BufferedWriter out;
	static BufferedReader in;
	static int c,noVertex,noFunction,noDemand,z,E,_no;
	static int limitedNo;
	static double alpha, beta,gama,theta;
	static nGraph g;
	static nGraph g_edit;
	static ArrayList<nFunction> functionArr;
	static ArrayList<nDemand> DemandArray;
	static double[][] link_load;
	static double[] node_load;
	static long _duration=0;
	static double maxlinkload=0.000000000;
	static double maxnodeload=0.0;
	static double acceptRatio=0.0;
	static Double[] zero ={0.0,0.0,0.0};
	static ArrayList<ArrayList<Integer>> solution_node;
	static ArrayList<ArrayList<Integer>> solution_func;
	static ArrayList<Integer> solution_id;
	static Vector<Vector<Double>> dataReal;
	static double prob;
	static ArrayList<Pair> funLoc;
	static ArrayList<Integer> h ;
	static boolean fl=false;
	static int flag = 0;
	static int source=-1;
	static int destination = -1;
	static int importNo =0;
	static boolean anchorNode = false;
	static double default_p;
	static double default_b;
	static ArrayList<ArrayList<Pair>> copyLinks ;
	
	public static double getLamdaF(int id)
	{
		if(id==0) return -1.0;
		for(int i=0;i<functionArr.size();i++)
			if (functionArr.get(i).id() ==id)
				return functionArr.get(i).getLamda();
		return -1.0;
	}
	public static nFunction getFunction(int id)
	{
		if(id==0) return null;
		for(int i=0;i<functionArr.size();i++)
			if (functionArr.get(i).id() ==id)
				return functionArr.get(i);
		return null;
	}
	
	public static double getBwService(int id)
	{
		if(id==0) return 0;
		for(int i=0;i<DemandArray.size();i++)
			if(DemandArray.get(i).getId()==id)
				return DemandArray.get(i).getBw();
		return -1;
	}
	public static nDemand getDemand(int id)
	{
		for (int i=0;i<DemandArray.size();i++)
			if(DemandArray.get(i).getId()==id)
				return DemandArray.get(i);
		return null;
	}
	
	static ArrayList<List<Integer>> Dist;// Dist(u,v) is a distance between u and v
	public static boolean _Dist()
	{
		SimpleWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
		Dist = new ArrayList<List<Integer>>();
		for(int i=0;i<noVertex+1;i++)
		{
			ArrayList<Integer> temp= new ArrayList<Integer>();
        	for (int j=0;j<noVertex+1;j++)
        	{
        		if(i==j)
        			temp.add(0);
        		else
        			temp.add(-1);
        	}
        	Dist.add(temp);
		}
		for (int j=0;j<noVertex;j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        DefaultWeightedEdge[] e= new DefaultWeightedEdge[(noVertex*(noVertex-1))/2];
        int id=0;
        
        for (int j=0;j<noVertex-1;j++)
        {	        	
        	for(int k=j+1;k<noVertex;k++)
        	{
        		e[id]=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
        		g_i.setEdgeWeight(e[id], g.getEdgeWeight((j +1), (k+1)));
        		id++;
        	}
        }
        for(int i=0;i<noVertex-1;i++)
        	for (int j=i+1;j<noVertex;j++)
        	{
        		List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+(i+1), "node"+(j+1));
        		if(_p!=null)
        		{
        			Dist.get(i+1).set(j+1, _p.size());
        			Dist.get(j+1).set(i+1, _p.size());
        		}
        		else
        		{
        			Dist.get(i+1).set(j+1, -1);
        			Dist.get(j+1).set(i+1, -1);
        		}
        	} 
        return true;
        
	}
	
	public static ArrayList<Integer> ShortestPath(int src, int dest, ExGraph _g,double maxBw,ArrayList<ArrayList<Integer>> mark,boolean flag)
	{
		ArrayList<Integer> _shortestPath = new ArrayList<Integer>();
		//SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
		SimpleWeightedGraph<String, DefaultWeightedEdge> g_i = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
        		
		for (int j=0;j<_g.getV();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(_g.getV()*(_g.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<_g.getV();j++)
        {	        	
        	for(int k=j+1;k<_g.getV();k++)
        	{
        		if(g.getEdgeWeight(j+1, k+1)>=maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e, _g.getEdgeWeight((j+1), (k+1)));
        		}
        	}
        } 
        for(int i=0;i<mark.size();i++)
        {
        	for (int j=0;j<(mark.get(i).size()/3+1);j++)
        	{
        		int del= UtilizeFunction.randInt(0, mark.get(i).size()-2);
        		g_i.removeEdge("node"+mark.get(i).get(del), "node"+mark.get(i).get(del+1));
        	}
        }
        List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        int source;
		if(_p!=null)
		{
			_shortestPath.add(src);
			source=src;
			while (_p.size()>0)
			{	
				int ix =0;
				for(int l=0;l<_p.size();l++)
				{
					int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
					int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
					if( int_s == source )
					{
						_shortestPath.add(int_t);
						source = int_t;
						ix = l;
						g_edit.setEdgeWeight(int_s, int_t, g_edit.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
					if( int_t == source)
					{
						_shortestPath.add(int_s);
						source = int_s;
						ix = l;
						g_edit.setEdgeWeight(int_s, int_t, g_edit.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
				}
				_p.remove(ix);
			}
//			for(int _i:_shortestPath)
//				{
//					System.out.print(_i+",");
//				}						
		}
		else
		{
			//System.out.print("khong tim duoc duong di giua"+src+"va"+ dest);
			return null;
			
		}
        
        
		return _shortestPath;
	}
	
	public static ArrayList<Integer> ShortestPath(int src, int dest, nGraph _g,double maxBw)
	{
		ArrayList<Integer> _shortestPath = new ArrayList<Integer>();
		//SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
        SimpleWeightedGraph<String, DefaultWeightedEdge> g_i = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
		for (int j=0;j<g.getV();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(g.getV()*(g.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<g.getV();j++)
        {	        	
        	for(int k=j+1;k<g.getV();k++)
        	{
        		if(j!=k&&_g.getEdgeWeight(j+1, k+1)>=maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e, g.getEdgeWeight((j+1), (k+1)));
        		}
        	}
        }       
        List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        int source;
		if(_p!=null)
		{
			_shortestPath.add(src);
			source=src;
			while (_p.size()>0)
			{	
				int ix =0;
				for(int l=0;l<_p.size();l++)
				{
					int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
					int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
					if( int_s == source )
					{
						_shortestPath.add(int_t);
						source = int_t;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
					if( int_t == source)
					{
						_shortestPath.add(int_s);
						source = int_s;
						ix = l;
						//_g.setEdgeWeight(int_s, int_t, _g.getEdgeWeight(int_s, int_t)-maxBw);
						break;
					}
				}
				_p.remove(ix);
			}
//			for(int _i:_shortestPath)
//				{
//					System.out.print(_i+",");
//				}						
		}
		else
		{
			//System.out.print("khong tim duoc duong di giua "+src+" va "+ dest);
			return null;
			
		}
        
        
		return _shortestPath;
	}
	
	
	
	public static ArrayList<Integer> ShortestPath(int src, int dest, double maxBw)
	{
		ArrayList<Integer> _shortestPath = new ArrayList<Integer>();
		//SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
		SimpleWeightedGraph<String, DefaultWeightedEdge> g_i = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
		for (int j=0;j<g_edit.getV();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(g_edit.getV()*(g_edit.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<g_edit.getV();j++)
        {	        	
        	for(int k=j+1;k<g_edit.getV();k++)
        	{
        		if(g_edit.getEdgeWeight(j+1, k+1)>=maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e, g.getEdgeWeight((j+1), (k+1)));
	        		//id++;
        		}
        	}
        }       
        List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        int source;
		if(_p!=null)
		{
			_shortestPath.add(src);
			source=src;
			while (_p.size()>0)
			{	
				int ix =0;
				for(int l=0;l<_p.size();l++)
				{
					int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
					int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
					if( int_s == source )
					{
						_shortestPath.add(int_t);
						source = int_t;
						ix = l;
						break;
					}
					if( int_t == source)
					{
						_shortestPath.add(int_s);
						source = int_s;
						ix = l;
						break;
					}
				}
				_p.remove(ix);
			}
//			for(int _i:_shortestPath)
//				{
//					System.out.print(_i+",");
//				}						
		}
		else
		{
			//System.out.print("khong tim duoc duong di giua"+src+"va"+ dest);
			return null;
			
		}
        
        
		return _shortestPath;
	}
	
	public static ArrayList<ArrayList<Integer>> allShortestPath(int src, int dest,nGraph _g, double maxBw)
	{
		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
		ArrayList<Link> linkSet = new ArrayList<>();
		//SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleDirectedWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class);
		SimpleWeightedGraph<String, DefaultWeightedEdge> g_i = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
		for (int j=0;j<_g.getV();j++)
        {
        	g_i.addVertex("node"+(j+1));
        }
        //DefaultWeightedEdge[] e= new DefaultWeightedEdge[(g_edit.getV()*(g_edit.getV()-1))/2];
        //int id=0;        
        for (int j=0;j<_g.getV();j++)
        {	        	
        	for(int k=j+1;k<_g.getV();k++)
        	{
        		if(_g.getEdgeWeight(j+1, k+1)>=maxBw)
        		{
        			DefaultWeightedEdge e=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		//g_i.setEdgeWeight(e, _g.getEdgeWeight((j+1), (k+1)));
        			g_i.setEdgeWeight(e, 1.0);
        		}
        	}
        }       
        //List<DefaultWeightedEdge> _p =   DijkstraShortestPath.findPathBetween(g_i, "node"+src, "node"+dest);
        FloydWarshallShortestPaths<String,DefaultWeightedEdge> floyGraph = new FloydWarshallShortestPaths<>(g_i);
        String srcStr = "node"+src;
        String destStr ="node"+ dest;
        GraphPath<String, DefaultWeightedEdge> spLst = floyGraph.getShortestPath(srcStr, destStr);
        
		if(spLst!=null)
		{
			srcStr= spLst.getStartVertex();
	        destStr = spLst.getEndVertex();
	        for (DefaultWeightedEdge i: spLst.getEdgeList())
	        {
	        	String strStart = g_i.getEdgeSource(i);
	        	String strEnd = g_i.getEdgeTarget(i);
	        	int int_s =Integer.parseInt(strStart.replaceAll("[\\D]", ""));
				int int_t =Integer.parseInt(strEnd.replaceAll("[\\D]", ""));
				linkSet.add(new Link(int_s, int_t));
				System.out.print("["+int_s+","+ int_t+"]" + ";");
	        }  
	        System.out.println();
	        //xet tung dinh o trong linkSet

        	
        	int start =src;
        	Queue<Integer> startLst = new LinkedList<>(); 
        	startLst.add(src);
	        int lenLinkSet =linkSet.size();
	        _shortestPath.add(src);
	        _shortestPathLst.add(_shortestPath);
	        while (lenLinkSet>0)
	        {
	        	int lenShortestList = _shortestPathLst.size();
	        	for (int i=0;i<lenShortestList;i++)
    			{
    				_shortestPath = _shortestPathLst.get(i);
    				start = _shortestPath.get(_shortestPath.size()-1);
    				ArrayList<Integer> endLst = new ArrayList<>(); 
            		for (Link l : linkSet)
    	        	{
    	        		if(l.getStart()==start)
    	        		{
    	        			endLst.add(linkSet.indexOf(l));//luu lai index cua link l in linkSet
    	        		} 	        		
    	        	}
            		if(endLst.size()>0)
            		{
            			ArrayList<Integer> tempPath =_shortestPath;
                		_shortestPath.add(linkSet.get(endLst.get(0)).getEnd());
                		_shortestPathLst.set(i, _shortestPath);
                		for (int idEnd=1;idEnd < endLst.size();idEnd++)
                		{
                			_shortestPath = tempPath;
                			_shortestPath.add(linkSet.get(idEnd).getEnd()); //and them end node vao mang
                			_shortestPathLst.add(_shortestPath);
                		}
                		for(int idLink:endLst)
                		{
                			linkSet.remove(idLink);
                		}        
            		}
            		    		
    			}
	        	lenLinkSet =linkSet.size();
	        }
		}
		else
		{
			//System.out.print("khong tim duoc duong di giua"+src+"va"+ dest);
			return null;
			
		}       
        for (int i = 0;i< _shortestPathLst.size();i++)
        {
        	System.out.print(i+ ": [");
        	for (int j=0;j<_shortestPathLst.get(i).size();j++)
        		System.out.print(_shortestPathLst.get(i).get(j)+" ");
        	System.out.println("]");
        }
		return _shortestPathLst;
	}
	
	
	public static boolean nonNFV(String outFile)
	{
		List<DefaultWeightedEdge> _p;
		List<Integer> nodeList;
		//final long startTime = System.currentTimeMillis();
		
		try {
			File file = new File(outFile);
			out = new BufferedWriter(new FileWriter(file));
			int[] rank_service= new int[noDemand];
			if(noDemand>1)
			{
				for (int i=0;i<noDemand;i++)
					rank_service[i]= i+1;
				for(int i=0;i<noDemand-1;i++)
				{
					int temp=i;
					for (int j=i+1;j<noDemand;j++)
						if(getDemand(rank_service[j]).getBw()>getDemand(rank_service[temp]).getBw())
							temp=j;
					int k= rank_service[i];
					rank_service[i]=rank_service[temp];
					rank_service[temp]=k;
				}
			}
			else
			{
				rank_service[0]=1;
			}
			SimpleWeightedGraph<String, DefaultWeightedEdge>  g_i = new SimpleWeightedGraph<String, DefaultWeightedEdge>(DefaultWeightedEdge.class); 
	        for (int j=0;j<noVertex;j++)
	        {
	        	g_i.addVertex("node"+(j+1));
	        }
	        DefaultWeightedEdge[] e= new DefaultWeightedEdge[(noVertex*(noVertex-1))/2];
	        int id=0;
	        
	        for (int j=0;j<noVertex-1;j++)
	        {	        	
	        	for(int k=j+1;k<noVertex;k++)
	        	{
	        		e[id]=g_i.addEdge("node"+(j+1),"node"+(k+1));	        			
	        		g_i.setEdgeWeight(e[id], g.getEdgeWeight((j +1), (k+1)));
	        		id++;
	        	}
	        }
	        int i=0;
			while(i<noDemand)
			{
				//tim duong di cho moi demand
				//tuy thuoc vao bandwidth
				nDemand _d= getDemand(rank_service[i]);
				if(_d.getSrc()==_d.getDest())
					
				{
					out.write("["+_d.getSrc()+"]");
					out.newLine();
				}
				else
				{
				//remove edges which haven't enough capacity
				DefaultWeightedEdge[] removed_edge = new DefaultWeightedEdge[id];
				int no_removed_edge =0;
				for( DefaultWeightedEdge v:g_i.edgeSet())
				{
					if(g_i.getEdgeWeight(v)<_d.getBw())
						removed_edge[no_removed_edge++]=v;				
				}
				for (int j=0;j<no_removed_edge;j++)
					g_i.removeEdge(removed_edge[j]);
				_p =  DijkstraShortestPath.findPathBetween(g_i, "node"+_d.getSrc(), "node"+_d.getDest());
				
				int source = _d.getSrc();
				if(_p!=null)
				{
					
					nodeList = new ArrayList<Integer>();
					// sau do chon duong ngan nhat 
					nodeList.add(source);
					while (_p.size()>0)
					{	
						int ix =0;
						for(int l=0;l<_p.size();l++)
						{
							int int_s =Integer.parseInt(g_i.getEdgeSource(_p.get(l)).replaceAll("[\\D]", ""));
							int int_t =Integer.parseInt(g_i.getEdgeTarget(_p.get(l)).replaceAll("[\\D]", ""));
							//value_bandwidth +=g.getEdgeWeight(int_s, int_t) * g.getPriceBandwidth() ;
							//value_final +=g.getEdgeWeight(int_s, int_t) * g.getPriceBandwidth() ;	
							if( int_s == source )
							{
								nodeList.add(int_t);
								source = int_t;
								ix = l;
								g.setEdgeWeight(int_s, int_t, g.getEdgeWeight(int_s, int_t)-_d.getBw());
								break;
							}
							if( int_t == source)
							{
								nodeList.add(int_s);
								source = int_s;
								ix = l;
								g.setEdgeWeight(int_s, int_t, g.getEdgeWeight(int_s, int_t)-_d.getBw());
								break;
							}
						}
						_p.remove(ix);	
					}
					//in ra file
					out.write("[");
					for(int _i:nodeList)
					{
						//System.out.print(_i+",");
						out.write(_i+", ");
					}
					//System.out.println();
					out.write("]");
					out.newLine();
				}
				else
				{
					//khong tim duoc duong di -> khong tim ra giai phap
					return false;
				}
				}
				//value_bandwidth +=weight_path * g.getPriceBandwidth() *_d.bwS();
				i++;			
			
			}
			//_duration = System.currentTimeMillis() - startTime;
			//System.out.println(_duration);
			//out.write("Runtime (mS): "+ _duration);
			out.newLine();
			//out.write("Value bandwidth: "+ value_bandwidth);
			
		} catch ( IOException e1 ) {
			e1.printStackTrace();
			} finally {
				if ( out != null )
					try {
						out.close();
						} catch (IOException e) {
							e.printStackTrace();}
				}    
	try {
  		out.close();
  		} catch (IOException e2) {
  			e2.printStackTrace();
  			}
			return true;
	}
	static List<List<Integer>> v_solution;
	static List<List<Integer>> f_solution;
	static ArrayList<Integer> list_v = new ArrayList<Integer>();
	static ArrayList<Integer> list_f = new ArrayList<Integer>();
	static int f_id=0;
	static boolean _finished=false;
	static List<List<Integer>> BFStree;
	static int START, END;
	public static void DFS(double bwMax,LinkedList<Integer> visited,ArrayList<ArrayList<Integer>> _DFSTree)
	{
		ArrayList<Integer> _inter= new ArrayList<Integer>();
		int last= visited.getLast();
		//LinkedList<String> nodes = graph.adjacentNodes(visited.getLast());
		LinkedList<Integer> nodes = new LinkedList<>();
		for (int i=0;i<g_edit.getV();i++)
		{
			if(g_edit.getEdgeWeight(last, i+1)>bwMax)
				nodes.add(i+1);
		}
        // examine adjacent nodes
        for (Integer node : nodes) {
            if (visited.contains(node)) {
                continue;
            }
            if (node.equals(END)) {
                visited.add(node);
                for (Integer nodeP : visited) {
                	_inter.add(nodeP);
                }
                _DFSTree.add(_inter);
                visited.removeLast();
                break;
            }
        }
        for (Integer node : nodes) {
            if (visited.contains(node) || node.equals(END)) {
                continue;
            }
            visited.addLast(node);
            DFS(bwMax, visited,_DFSTree);
            visited.removeLast();
        }
        nodes=null;
	}
	public static boolean BFS(int V,int start, int finish, double bwMax,ArrayList<ArrayList<Integer>> BFStree)
	{
		//BFStree = new ArrayList<List<Integer>>();
		int color[]= new int[V+1];
		int back[]= new int[V+1];
		Queue<Integer> qList= new LinkedList<Integer>();
		for (int i=0;i<V;i++)
		{
			//color = 0-> chua di qua lan nao
			//color = 1 -> da di qua 1 lan
			//color = 2 -> tat ca dinh ke da duoc danh dau
			color[i+1]=0;
			back[i+1]=-1;//mang luu cac dinh cha cua i
		}
		color[start]=1;
		qList.add(start);
		while(!qList.isEmpty())
		{
			//lay gia tri dau tien trong hang doi
			int u=qList.poll();
			if(u==finish)
			{
				//tim duoc duong roi
				list_v = new ArrayList<Integer>();
				return_path(start, finish, back);
				BFStree.add(list_v);
				list_v=null;
				list_v = new ArrayList<Integer>();
			}
			else
			{
				//tim dinh ke chua di qua lan nao
				for(int v=0;v<V;v++)
				{
					if(g_edit.getEdgeWeight(u, v+1)>=bwMax && color[v+1]==0)
					{
						color[u]=1;
						//luu lai nut cha cua v
						back[v+1]=u;
						qList.add(v+1);
					}
				}
				//da duyet het dinh ke cua dinh u
				color[u]=2;				
			}
		}
		return true;
		
	}
	
	
	public static boolean return_path(int u, int v,int back[])
	{
		
		if(u==v)
			list_v.add(v);
		else
		{
			if(back[v]==-1)
				return false;
			else
			{
				return_path(u, back[v], back);
				list_v.add(v);
			}
		}
		return true;
			
	}
	public static ArrayList<Integer> noFunctionAlg(nDemand _d, nGraph _g)
	{
		funLoc = new ArrayList<>();
		ArrayList<ArrayList<Integer>> pathLst = new ArrayList<>();
		int _src = _d.getSrc();
		int _dest= _d.getDest();
		pathLst = shortestPaths(_src, _dest, _g, _d.getBw(),_d.getProcessReq());
		if(pathLst!=null && pathLst.size()>0)
		{
			fl = true;
			return pathLst.get(0);
			
		}
		else
		{
			fl=false;
			return null;
		}
	}
	public static ArrayList<Integer> GreedyForward(nDemand _d, nGraph _g)
	{
		fl=false;
		funLoc = new ArrayList<>();
		boolean  _flag=false;
		ArrayList<Integer> _sol = new ArrayList<Integer>();
		ArrayList<ArrayList<Integer>> pathLst = new ArrayList<>();
		nGraph g_tam= new nGraph(_g.cap,_g.w);
		int _src = _d.getSrc();
		int _dest= _d.getDest();
		ArrayList<Integer> _fLst=_d.getFunctions();
		if(_fLst.size()==0)
		{
			//tinh duong di ngan nhat tu src den dest
			//path= ShortestPath(_d.getSrc(),_d.getDest(),_g, _d.getBw());
			pathLst = shortestPaths(_src, _dest, _g, _d.getBw(),_d.getProcessReq());
			if(pathLst!=null && pathLst.size()>0)
				return pathLst.get(0);
			else
				return null;
		}
		ArrayList<Integer> _z1= getFunction(_fLst.get(0)).getVnfNode();//tap z1
		int node1=-1;
		int node2=-1;
		int minNode=-1;
		ArrayList<Integer> _sp = new ArrayList<>();//luu tru duong di ngan nhat hien tai
		int _minVal = Integer.MAX_VALUE;//luu tru do dai ngan nhat cua duong di.
		
		ArrayList<Integer> removedId = new ArrayList<>();
		for (int _id2=0;_id2<_z1.size();_id2++)
		{
			node2 = _z1.get(_id2);
			if((getFunction(_fLst.get(0)).getLamda()+ _d.getProcessReq())>g_tam.getCap(node2))
			{
				removedId.add(_id2);
			}
		}
		for(int i=0;i<removedId.size();i++)
			_z1.remove(removedId.get(i));
		// Chon 1 duong ngan nhat tu src den tap z1 ->
		_sp = SP_GreedyForward(_src, _z1,_g, _d.getBw(),_d.getProcessReq());
		if(_sp!=null)
		{
			_flag=false;
			node1=_sp.get(_sp.size()-1);
			g_tam = new nGraph(_g.cap, _g.w);
			double c_temp= g_tam.getCap(node1)-getFunction(_fLst.get(0)).getLamda();
			g_tam.setCap(node1,c_temp );
			for(int i=0;i<_sp.size()-1;i++)
			{
				if(g_tam.getEdgeWeight(_sp.get(i), _sp.get(i+1))<_d.getBw())
				{
					_flag=true;
					break;
					}
				else
					g_tam.setEdgeWeight(_sp.get(i), _sp.get(i+1),g_tam.getEdgeWeight(_sp.get(i), _sp.get(i+1))-_d.getBw() );
				
			}
			for (int i=0;i<_sp.size();i++)
			{
				if(g_tam.getCap(_sp.get(i))<_d.getProcessReq())
				{
					_flag=true;
					break;
					}
				else
				{
					c_temp= g_tam.getCap(_sp.get(i))-_d.getProcessReq();
					g_tam.setCap(_sp.get(i),c_temp );
				}
			}
			if(!_flag)
			{
				_minVal = _sp.size();
				minNode= node1;
			}
			
		}
		
		if (minNode ==-1)
		{
			//truong hop ko the tim duoc bat ky 1 node nao trong z1 -> demand ko thoa man
			fl=false;
			return null;
		}
		else
		{
			_flag=true;
			node1= minNode;
			//truoc het pai add duong di ngan nhat giua src va z1 vao _sol
			
			for (int _id1=0;_id1<_sp.size();_id1++)
				_sol.add(_sp.get(_id1));
			//cap nhat lai do thi g_tam
			
			for (int _node=0;_node<_sp.size()-1;_node++)
			{
				double w_temp= _g.getEdgeWeight(_sp.get(_node), _sp.get(_node+1))-_d.getBw();
				_g.setEdgeWeight(_sp.get(_node), _sp.get(_node+1),w_temp );
				double c_temp= _g.getCap(_sp.get(_node))-_d.getProcessReq();
				_g.setCap(_sp.get(_node),c_temp );
				
			}
//			for (int _node=0;_node<_sp.size();_node++)
//			{
//				double c_temp= _g.getCap(_sp.get(_node))-_d.getProcessReq();
//				_g.setCap(_sp.get(_node),c_temp );
//			}			
			double c_temp= _g.getCap(node1)-getFunction(_fLst.get(0)).getLamda();
			_g.setCap(node1,c_temp );
			funLoc.add(new Pair(node1,_fLst.get(0)));
			
			//thuc hien voi cac cap z2, z3..
			for (int _id1=1;_id1<_fLst.size();_id1++)
			{
				_flag=false;
				minNode=-1;
				_minVal=Integer.MAX_VALUE;
				ArrayList<Integer> _zi= getFunction(_fLst.get(_id1)).getVnfNode();
				removedId = new ArrayList<>();
				for (int _id2=0;_id2<_zi.size();_id2++)
				{
					node2 = _zi.get(_id2);
					if((getFunction(_fLst.get(_id1)).getLamda()+ _d.getProcessReq())>g_tam.getCap(node2))
					{
						removedId.add(_id2);
					}
				}
				for(int i=0;i<removedId.size();i++)
					_zi.remove(removedId.get(i));
				_sp=SP_GreedyForward(node1, _zi,_g, _d.getBw(),_d.getProcessReq());
				if(_sp!=null)
				{
					node2= _sp.get(_sp.size()-1);
					_flag=false;
					g_tam = new nGraph(_g.cap, _g.w);
					c_temp= g_tam.getCap(node2)-getFunction(_fLst.get(_id1)).getLamda();
					g_tam.setCap(node2,c_temp );
					for(int i=0;i<_sp.size()-1;i++)
					{
						if(g_tam.getEdgeWeight(_sp.get(i), _sp.get(i+1))<_d.getBw())
						{
							_flag=true;
							break;
							}
						else
							g_tam.setEdgeWeight(_sp.get(i), _sp.get(i+1),g_tam.getEdgeWeight(_sp.get(i), _sp.get(i+1))-_d.getBw() );
						
					}
					for (int i=0;i<_sp.size();i++)
					{
						if(g_tam.getCap(_sp.get(i))<_d.getProcessReq())
						{
							_flag=true;
							break;
							}
						else
						{
							c_temp= g_tam.getCap(_sp.get(i))-_d.getProcessReq();
							g_tam.setCap(_sp.get(i),c_temp );
						}
					}
					if(!_flag)
					{
						_minVal = _sp.size();
						minNode= node2;//luu lai node co gia tri nho nhat
					}
				}			
				if(minNode==-1)//neu ko tim duoc duong di ngan nhat giua 2 cap zi va zj -> demand nay ko the tim ra duong di
				{
					_flag=false;
					break;
				}
				else
				{
					_flag=true;
					for (int _id2=1;_id2<_sp.size();_id2++)
						_sol.add(_sp.get(_id2));
					node1=minNode;
					//cap nhat lai do thi _g
					
					for (int _node=0;_node<_sp.size()-1;_node++)
					{
						double w_temp= _g.getEdgeWeight(_sp.get(_node), _sp.get(_node+1))-_d.getBw();
						_g.setEdgeWeight(_sp.get(_node), _sp.get(_node+1),w_temp );
						c_temp= _g.getCap(_sp.get(_node))-_d.getProcessReq();
						_g.setCap(_sp.get(_node),c_temp );
						
					}
					c_temp= _g.getCap(node1)-getFunction(_fLst.get(_id1)).getLamda();
					_g.setCap(node1,c_temp );
					funLoc.add(new Pair(node1,_fLst.get(_id1)));
				}
			}
			if(!_flag)//neu demand nay ko the tim ra yeu cau thoa man
			{
				fl=false;
				return null;
			}
			else 
			{
				//tim duong di giua zn va dest
				if(minNode != _dest)
				{
					if(_g.getCap(_dest)>=_d.getProcessReq())
					{
						ArrayList<Integer> dLst = new ArrayList<>();
						dLst.add(_dest);
						_sp= SP_GreedyForward(minNode, dLst,_g, _d.getBw(),_d.getProcessReq());
						if(_sp!=null)
						{
							for(int i=0;i<_sp.size()-1;i++)
							{
								if(_g.getEdgeWeight(_sp.get(i), _sp.get(i+1))<_d.getBw())
								{
									fl=false;
									return null;
									}
								else
									_g.setEdgeWeight(_sp.get(i), _sp.get(i+1),_g.getEdgeWeight(_sp.get(i), _sp.get(i+1))-_d.getBw() );
								
							}
							for(int i=0;i<_sp.size();i++)
							{
								if(_g.getCap(_sp.get(i))<_d.getProcessReq())
								{
									fl= false;
									return null;
									}
								else
								{
									c_temp= g_tam.getCap(_sp.get(i))-_d.getProcessReq();
									_g.setCap(_sp.get(i),c_temp );
								}
							}
							for (int _id3=1;_id3<_sp.size();_id3++)
								_sol.add(_sp.get(_id3));
						}
					}
				}
			}
			
		}	
		fl=true;
		return _sol;
	}
	public static boolean CheckFunc(nFunction _f, int n)
	{
		ArrayList<Integer> nodes = _f.getVnfNode();
		for (Integer i : nodes) {
			if(i==n)
				return true;
		}
		return false;
	}

	public static int indexOfSet(Link l,ArrayList<Link> set)
	{
		int id=-1;
		for(int i=0;i<set.size();i++)
			if(set.get(i).CompareTo(l))
				id=i;
		return id;
	}
	public static ArrayList<Link> ConnectionSetSimple(ArrayList<Integer> srcLst, ArrayList<Integer> destLst,double maxBandwidth)
	{
		ArrayList<Link> sets = new ArrayList<>();
		int V=g.getV();
		for (int i=0;i<V;i++)
			for (int j=0;j<V;j++)
			{
				if(!(srcLst.contains(i+1)&& srcLst.contains(j+1))||!(destLst.contains(i+1)&& destLst.contains(j+1)))
				{
					if (g.getEdgeWeight(i+1, j+1)>=maxBandwidth)
					{
						Link l= new Link(i+1, j+1);
						sets.add(l);
					}
				}
			}
		for (int i=0;i<srcLst.size();i++)
			for (int j=0;j<destLst.size();j++)
			{
				if(srcLst.get(i)==destLst.get(j))
				{
					Link l = new Link(srcLst.get(i), destLst.get(j));
					sets.add(l);
				}
				
			}
		return sets;
		
	
	
	}
	public static ArrayList<Link> ConnectionSets(int src, int dest)
	{		
		ArrayList<Link> sets = new ArrayList<>();
		ArrayList<Link> setZero = new ArrayList<>();
		ArrayList<Link> idLst = new ArrayList<>();
		nGraph g_tam = new nGraph(g.cap,g.w);
		for (int i=0;i<g.getV();i++)
			for (int j=0;j<g.getV();j++)
			{
				if (g.getEdgeWeight(i+1, j+1)>0)
				{
					Link l= new Link(i+1, j+1);
					setZero.add(l);
				}
			}
		ArrayList<Integer> p = ShortestPath(src, dest, g_tam,0.0000001);
		if(p!=null)
		{
			for(int i=0;i<p.size()-1;i++)
			{
				Link l= new Link(p.get(i),p.get(i+1));
				sets.add(l);
				//remove l from setZero
				int id= indexOfSet(l, setZero);
				if(id!=-1)
					setZero.remove(id);
				g_tam.setEdgeWeight(p.get(i), p.get(i+1), 0);
				
			}
		}
		int len = setZero.size();
		while(len>0)
		{
			idLst = new ArrayList<>();
			int id= UtilizeFunction.randInt(0, len-1);
			Link l = setZero.get(id);
			ArrayList<Integer> p1 = ShortestPath(src, l.getStart(), g_tam,0.0000001);
			ArrayList<Integer> p2 = ShortestPath(l.getEnd(), dest, g_tam,0.0000001);
			if(p1!=null && p2!=null)
			{
				//add p1, p2, l to set
				sets.add(l);
				idLst.add(l);
					//setZero.remove(id1);
				for(int i=0;i<p1.size()-1;i++)
				{
					Link l1= new Link(p1.get(i),p1.get(i+1));
					sets.add(l1);
					//remove l from setZero
					idLst.add(l1);
						//setZero.remove(id1);
					g_tam.setEdgeWeight(p1.get(i), p1.get(i+1), 0);
					
				}
				for(int i=0;i<p2.size()-1;i++)
				{
					Link l1= new Link(p2.get(i),p2.get(i+1));
					sets.add(l1);
					//remove l from setZero
					idLst.add(l1);
						//setZero.remove(id1);
					g_tam.setEdgeWeight(p2.get(i), p2.get(i+1), 0);
					
				}
				//remove p1,p2, l from setzero
			}
			else
			{
				//remove l from setzero
				idLst.add(l);
					//setZero.remove(id1);
			}
			g_tam.setEdgeWeight(l.getStart(), l.getEnd(), 0);
			
			for(Link i:idLst)
			{
				setZero.remove(i);
			}
			len = setZero.size();	
			p1=null;
			p2=null;
		}
		p=null;
		return sets;
		
	}
	
	//tra ve gia tri cua tap set neu la giong nhau
	public static wLink linkContain_wLinkList (Link l,ArrayList<wLink> wl)
	{
		for (wLink _wl: wl)
		{
			if(_wl.getStart()==l.getStart() && _wl.getEnd() == l.getEnd())
				return _wl;
		}
		return null;
	}
	
	public static ArrayList<Integer> compairToLink (Link l, wLink wL)
	{
		if(l.getStart()==wL.getStart() && l.getEnd() == wL.getEnd())
			return wL.getCnnSet();
		else
			return null;
	}
	public static nGraph ExpandedGraphNew(nGraph _g, nDemand _d, ArrayList<wLink> violatedLink, ArrayList<Node> updatedNode)
	{
		int NumV=0;
		int src = _d.getSrc();
		int dest= _d.getDest();
		int lastNode = 0;
		ArrayList<Integer> fLst = _d.getFunctions();
		Vector<Double> k = new Vector<>();
		h = new ArrayList<Integer>();//Function h is a mapping from an exspanded node to an origin node
		ArrayList<WeitEdge> edgeLst= new ArrayList<>();
		k.add(_g.getCap(src));
		h.add(src);
		source = 1;
		ArrayList<Integer> ZSize = new ArrayList<>();
		ArrayList<ArrayList<Integer>> Z = new ArrayList<>();
		ArrayList<Integer> Ztam= new ArrayList<>();
		
		for(int i=0;i<fLst.size();i++)
		{
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			Ztam= new ArrayList<>();
			int dem=0;
			for(int j=0;j<Zi.size();j++)
			{
				if(getFunction(fLst.get(i)).getLamda()<=_g.getCap(Zi.get(j)))
				{
					dem++;	
					boolean violateNode = false;
					Node _nodeTemp = new Node(Zi.get(j));
					if(updatedNode.size()>0)
					{
						for (int id =0;id<updatedNode.size();id++)
						{
							if(updatedNode.get(id).CompareTo(_nodeTemp))
							{
								violateNode=true;
								ArrayList<Integer> setNode = updatedNode.get(id).getvSetLst();
								if(setNode.contains(i+1))
								{
									Ztam.add(Zi.get(j));
									k.add(_g.getCap(Zi.get(j)));
									h.add(Zi.get(j));
								}							
							}
						}
					}
					
					if(!violateNode)
					{
						Ztam.add(Zi.get(j));
						k.add(_g.getCap(Zi.get(j)));
						h.add(Zi.get(j));
					}
					
				}
		
			}
			Z.add(Ztam);
			ZSize.add(dem);
			NumV=NumV+dem;
		}
		
		
		k.add(_g.getCap(dest));
		h.add(dest);
		NumV=NumV+2;//tinh ca dau va cuoi 0->lastnode-1;
		destination=NumV;
		ArrayList<Integer> Z1 = new ArrayList<>();
		ArrayList<Integer> Z2= new ArrayList<>();
		//ArrayList<Integer> Ztam= new ArrayList<>();
		int node1=-1;
		int node2 =-1;
		for (int i=-1;i<fLst.size();i++)
		{
			
			//last node truoc Zi+1		
			if(i==-1)
			{
				node1 = 0;
				Z1 = new ArrayList<>();
				Z1.add(src);
				node2 = 1;
			}
			else
			{
				node1=1;
				for (int temp=0;temp<i;temp++)
					node1 = node1+ ZSize.get(temp);//last node truoc Zi
				node2= node1 + ZSize.get(i);
				
				Z1 = Z.get(i);
				//Z1 = getFunction(fLst.get(i)).getVnfNode();
				
			}
			if(i==fLst.size()-1)
			{
				Z2= new ArrayList<>();
				Z2.add(dest);				
			}
			else
			{
				Z2 = Z.get(i+1);
			}
			
			//add tat ca cac dinh trong G
			//ArrayList<Integer> nodeLst = new ArrayList<>();
			for (int j=0;j<_g.getV();j++)
			{
				//nodeLst.add(j+1);				
				k.add(_g.getCap(j+1));
				h.add(j+1);
			}
			lastNode = NumV;
			NumV+=_g.getV();
			
			//add tat ca cac link tu s_k den s_K+1
			for(int j1=0;j1<Z1.size();j1++)
			{
				for(int j2=0;j2<_g.getV();j2++)
				{
					if(Z1.get(j1)==j2+1)
						edgeLst.add(new WeitEdge(node1+j1+1, lastNode+j2+1, 100.0));//truong hop canh zero
				}
			}
			
			for(int j1=0;j1<_g.getV();j1++)
			{
				for (int j2=0;j2<Z2.size();j2++)
				{
					if(j1+1==Z2.get(j2))
						edgeLst.add(new WeitEdge(lastNode+j1+1, node2+j2+1, 100.0));//truong hop canh zero
				}
				for(int j2=0;j2<_g.getV();j2++)
				{
					if(j1!=j2 && _g.getEdgeWeight(j1+1, j2+1)>=_d.getBw())
					{
						wLink _l = new wLink(j1+1, j2+1, 1, null);
						
						boolean violateLink = false;
						for (int id =0;id<violatedLink.size();id++)
						{
							if(violatedLink.get(id).CompareTo(_l))
							{
								violateLink=true;
								ArrayList<Integer> setLink = violatedLink.get(id).getCnnSet();
								if(setLink.contains(i+2))
								{
									edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
								}	
								break;
							}
						}
						if(!violateLink)
						{
							edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
						}
					}
				}
			}
		}
		
		
		nGraph g_save = new nGraph(NumV);
		
		System.out.println("Number of Extended Link: "+edgeLst.size());
		if(edgeLst.size()==0)
			return null;
        for (WeitEdge edges : edgeLst) {
        	int s = edges.getO();
        	int t = edges.getD();
			double w= edges.getW();
			g_save.setEdgeWeight(s, t, w);
		}
	   	for (int i=0;i<g.getV();i++)
       {
	   		g_save.setCap(i+1, k.get(i));
       }    
	   	//noVertex = g_save.getV();
	   	edgeLst =null;
	   	
		
		return g_save;
		
	
	
	
	}
	public static nGraph extendGraph(nGraph _g,nDemand _d,Double[][][] _x)
	{
		double proReq = _d.getProcessReq();
		double bw= _d.getBw();

		int NumV=_g.getV();
		source = _d.getSrc();
		destination= _d.getDest();
		int lastNode = 0;
		ArrayList<Integer> fLst = _d.getFunctions();
		Vector<Double> k = new Vector<>();
		h = new ArrayList<Integer>();//Function h is a mapping from an exspanded node to an origin node
		ArrayList<WeitEdge> edgeLst= new ArrayList<>();
		//add node and link !=0
		
		
		for (int i=0;i<fLst.size()+1;i++)
		{
			for(int j1=0;j1<NumV;j1++)
			{
				k.add(_g.getCap(j1+1));
				
			}
		}
		lastNode=0;
		for (int i=0;i<fLst.size()+1;i++)
		{
			for (int j1=0;j1<NumV;j1++)
				for(int j2=0;j2<NumV;j2++)
				{
					if((j1!=j2)&&(_g.getCap(j1+1)>=proReq)&&(_g.getCap(j2+1)>=proReq) && (_x[j1][j2][i]>bw))
						edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _x[j1][j2][i]));
				}
			lastNode+=NumV;
		}
		
		//add link =0;
		lastNode =0;
		for (int i=0;i<fLst.size();i++)
		{
			
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			for(int j=0;j<Zi.size();j++)
			{
				if((getFunction(fLst.get(i)).getLamda()+_d.getProcessReq())<=_g.getCap(Zi.get(j)))
				{
					int node = Zi.get(j);
					if(_x[node-1][node-1][i]>=0)
						edgeLst.add(new WeitEdge(lastNode+node, lastNode+node+NumV, _x[node-1][node-1][i]));
					
				}
			}
			lastNode += NumV;
		}
		NumV = NumV*(fLst.size()+1);
		
		destination= destination+ NumV -_g.getV();
		nGraph g_save = new nGraph(NumV);
		
		System.out.println("Number of Extended Link: "+edgeLst.size());
		if(edgeLst.size()==0)
			return null;
        for (WeitEdge edges : edgeLst) {
        	int s = edges.getO();
        	int t = edges.getD();
			double w= edges.getW();
			//System.out.print("("+s+","+t+"),");
			g_save.setEdgeWeight(s, t, w);
		}
	   	for (int i=0;i<g_save.getV();i++)
       {
	   		g_save.setCap(i+1, k.get(i));
       }    
	   	edgeLst =null;   	
		
		return g_save;		
		
		
		
	}
	public static nGraph CreateExGraph(nGraph _g, nDemand _d)
	{
		destination=0;
		int NumV=0;
		int _V =_g.getV();
		double bw = _d.getBw();
		double req = _d.getProcessReq();
		int lastNode = 0;
		ArrayList<Integer> fLst = _d.getFunctions();
		Vector<Double> k = new Vector<>();
		h = new ArrayList<Integer>();//Function h is a mapping from an exspanded node to an origin node
		ArrayList<WeitEdge> edgeLst= new ArrayList<>();
		//add node and link !=0
		
		
		for (int i=0;i<fLst.size()+1;i++)
		{
			for(int j1=0;j1<_g.getV();j1++)
			{
				k.add(_g.getCap(j1+1));
				h.add(j1+1);
				NumV++;
				
			}
		}
		source = _d.getSrc();
		lastNode=0;
		for (int i=0;i<fLst.size()+1;i++)
		{
			for (int j1=0;j1<_V;j1++)
				for(int j2=0;j2<_V;j2++)
				{
					if(j1!=j2 && _g.getEdgeWeight(j1+1, j2+1)>=bw)
						if(_g.getCap(j1+1)>=req && _g.getCap(j2+1)>=req)
							edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1,j2+1)));
				}
			lastNode+=_V;
		}
		
		//add link =0;
		lastNode =0;
		for (int i=0;i<fLst.size();i++)
		{			
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			for(int j=0;j<Zi.size();j++)
			{
				if((getFunction(fLst.get(i)).getLamda()+req)<=_g.getCap(Zi.get(j)))
				{
					int node = Zi.get(j);
					edgeLst.add(new WeitEdge(lastNode+node, lastNode+node+_V, 100.0));
					
				}
			}
			lastNode += _V;
		}
		
		destination= _d.getDest()+ NumV -_g.getV();
		nGraph g_save = new nGraph(NumV);
		
		System.out.println("Number of Extended Link: "+edgeLst.size());
		if(edgeLst.size()==0)
			return null;
        for (WeitEdge edges : edgeLst) {
        	int s = edges.getO();
        	int t = edges.getD();
			double w= edges.getW();
			//System.out.print("("+s+","+t+"),");
			g_save.setEdgeWeight(s, t, w);
		}
	   	for (int i=0;i<g_save.getV();i++)
       {
	   		g_save.setCap(i+1, k.get(i));
       }    
	   	//noVertex = g_save.getV();
	   	edgeLst =null;   	
		
		return g_save;	
	}
	
	public static nGraph CreateExGraph(nGraph _g, nDemand _d, ArrayList<wLink> violatedLink, ArrayList<Node> updatedNode1,ArrayList<Node> updatedNode2)
	{
		int NumV=0;
		int lastNode = 0;
		int _V =_g.getV();
		double bw = _d.getBw();
		double req = _d.getProcessReq();
		ArrayList<Integer> fLst = _d.getFunctions();
		Vector<Double> k = new Vector<>();
		h = new ArrayList<Integer>();//Function h is a mapping from an exspanded node to an origin node
		ArrayList<WeitEdge> edgeLst= new ArrayList<>();
		
		//add node and link !=0
		
		
		for (int i=0;i<fLst.size()+1;i++)
		{
			for(int j1=0;j1<_g.getV();j1++)
			{
				k.add(_g.getCap(j1+1));
				h.add(j1+1);
				NumV++;
				
			}
		}
		
		ArrayList<Integer> deletedNode = new ArrayList<>();
		//updateNode2 la nhung node voi cac tap khong the co node nay duoc
		if(updatedNode2.size()>0)
		{
			for (int id =0;id<updatedNode2.size();id++)
			{
				Node _node = updatedNode2.get(id);
				for (int id1 = 0; id1<_node.getvSetLst().size();id1++)
				{
					int noSet= _node.getvSetLst().get(id1);
					int idNode = _node.getid() + _V *(noSet-1);
					deletedNode.add(idNode);
				}
			}
		}			
		
		
		source = _d.getSrc();
		
		for (int i=0;i<fLst.size()+1;i++)
		{
			for (int j1=0;j1<_V;j1++)
				for(int j2=0;j2<_V;j2++)
				{
					if(deletedNode.size()>0)
					{
						if(j1!=j2 && _g.getEdgeWeight(j1+1, j2+1)>=bw && !deletedNode.contains(j1+1) && !deletedNode.contains(j2+1))
						{	
							wLink _l = new wLink(j1+1, j2+1, 1, null);
							boolean violateLink = false;
							if(violatedLink.size()>0)
							{
								for (int id =0;id<violatedLink.size();id++)
								{
									if(violatedLink.get(id).CompareTo(_l))
									{
										violateLink=true;
										ArrayList<Integer> setLink = violatedLink.get(id).getCnnSet();
										if(setLink.contains(i+1))
										{
											edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
										}	
										break;
									}
								}
								if(!violateLink)
								{
									edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
								}
							}
							
						}
						else
						{
							edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
						}
					}
					else
					{
						if(j1!=j2 && _g.getEdgeWeight(j1+1, j2+1)>=bw)
						{	
							wLink _l = new wLink(j1+1, j2+1, 1, null);
							boolean violateLink = false;
							if(violatedLink.size()>0)
							{
								for (int id =0;id<violatedLink.size();id++)
								{
									if(violatedLink.get(id).CompareTo(_l))
									{
										violateLink=true;
										ArrayList<Integer> setLink = violatedLink.get(id).getCnnSet();
										if(setLink.contains(i+1))
										{
											edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
										}	
										break;
									}
								}
								if(!violateLink)
								{
									edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
								}
							}
							else
							{
								edgeLst.add(new WeitEdge(lastNode+j1+1, lastNode+j2+1, _g.getEdgeWeight(j1+1, j2+1)));
							}
							
						}
					}
					
				}
			lastNode+=_V;
		}
		
		//add link =0;
		lastNode =0;
		for (int i=0;i<fLst.size();i++)
		{
			
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			for(int j=0;j<Zi.size();j++)
			{
				if((getFunction(fLst.get(i)).getLamda()+req)<=_g.getCap(Zi.get(j)))
				{
					boolean violateNode = false;
					Node _nodeTemp = new Node(Zi.get(j));
					if(updatedNode1.size()>0)
					{
						for (int id =0;id<updatedNode1.size();id++)
						{
							if(updatedNode1.get(id).CompareTo(_nodeTemp))
							{
								violateNode=true;
								if(updatedNode1.get(id).getvSetLst().contains(i+1))
								{
									int node = Zi.get(j);
									
									edgeLst.add(new WeitEdge(lastNode+node, lastNode+node+_V, 100.0));
								}
								break;
							}
						}
					}
					
					if(!violateNode)
					{
						int node = Zi.get(j);
						
						edgeLst.add(new WeitEdge(lastNode+node, lastNode+node+_V, 100.0));
						
					}	
				}
			}
			lastNode += _V;
		}	
		
		
		destination= _d.getDest()+ NumV -_V;
		
		nGraph g_save = new nGraph(NumV);
		
		System.out.println("Number of Extended Link: "+edgeLst.size());
		if(edgeLst.size()==0)
			return null;
        for (WeitEdge edges : edgeLst) {
        	int s = edges.getO();
        	int t = edges.getD();
			double w= edges.getW();
			//System.out.print("("+s+","+t+"),");
			g_save.setEdgeWeight(s, t, w);
		}
	   	for (int i=0;i<g_save.getV();i++)
       {
	   		g_save.setCap(i+1, k.get(i));
       }    
	   	//noVertex = g_save.getV();
	   	edgeLst =null;   	
		
		return g_save;	
	}
	
	public static nGraph ConstructingSimpleGraph(nGraph _g,nDemand _d)
	{

		int NumV=0;
		int src = _d.getSrc();
		int dest= _d.getDest();
		int lastNode = 0;
		int idStart,idEnd;
		ArrayList<Integer> fLst = _d.getFunctions();
		ArrayList<Link> outLink = new ArrayList<>();
		Vector<Double> k = new Vector<>();
		h = new ArrayList<Integer>();//Function h is a mapping from an exspanded node to an origin node
		ArrayList<WeitEdge> edgeLst= new ArrayList<>();
		k.add(_g.getCap(src));
		h.add(src);
		source = 1;
		ArrayList<Integer> ZSize = new ArrayList<>();
		for(int i=0;i<fLst.size();i++)
		{
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			ZSize.add(Zi.size());
			NumV=NumV+Zi.size();
			for(int j=0;j<Zi.size();j++)
			{
				k.add(_g.getCap(Zi.get(j)));
				h.add(Zi.get(j));
				
			}
			for(int j1=0;j1<Zi.size();j1++)
			{
				for (int j2=0;j2<Zi.size();j2++)
				{
					if(Zi.get(j1)!=Zi.get(j2))
					{
						Link l = new Link(Zi.get(j1), Zi.get(j2));
						outLink.add(l);
						l= new Link(Zi.get(j2), Zi.get(j1));
						outLink.add(l);
//						if(_g.getEdgeWeight(Zi.get(j1),Zi.get(j2))>=_d.getBw())
//						{
//							Link l = new Link(Zi.get(j1), Zi.get(j2));
//							outLink.add(l);
//						}
					}
				}
				
			}
		}
		k.add(_g.getCap(dest));
		h.add(dest);
		NumV=NumV+2;//tinh ca dau va cuoi 0->lastnode-1;
		destination=NumV;
		ArrayList<Integer> Z1 = new ArrayList<>();
		ArrayList<Integer> Z2= new ArrayList<>();
		int node1=-1;
		int node2 =-1;
		for (int i=-1;i<fLst.size();i++)
		{
			
			//last node truoc Zi+1		
			if(i==-1)
			{
				node1 = 0;
				Z1 = new ArrayList<>();
				Z1.add(src);
				node2 = 1;
			}
			else
			{
				node1=1;
				for (int temp=0;temp<i;temp++)
					node1 = node1+ ZSize.get(temp);//last node truoc Zi
				node2= node1 + ZSize.get(i);
				Z1 = getFunction(fLst.get(i)).getVnfNode();
			}
			if(i==fLst.size()-1)
			{
				Z2= new ArrayList<>();
				Z2.add(dest);				
			}
			else
			{
				Z2 = getFunction(fLst.get(i+1)).getVnfNode();
			}
			ArrayList<Link> cnnSet = ConnectionSetSimple(Z1, Z2,_d.getBw());
			if(cnnSet!=null)
			{
				ArrayList<Integer> nodeLst = new ArrayList<>();//chua tat ca cac node chua ton tai trong do thi g -> phai add them vao
				for(Link l: cnnSet)
				{
					if(!Z1.contains(l.getStart())&&!Z2.contains(l.getStart()) && !nodeLst.contains(l.getStart()))
						nodeLst.add(l.getStart());
					if(!Z1.contains(l.getEnd())&&!Z2.contains(l.getEnd())&& !nodeLst.contains(l.getEnd()))
						nodeLst.add(l.getEnd());					
				}
				lastNode = NumV;//lastnode truoc khi add them node;
				for (int j=0;j<nodeLst.size();j++)
				{
					k.add(_g.getCap(nodeLst.get(j)));
					h.add(nodeLst.get(j));
				}
				NumV+= nodeLst.size();
				//cac node da duoc add, quan trong la add link-> dua no vao mot tap cac link
				for (Link l:cnnSet)
				{
					if(!outLink.contains(l))
					{
						idStart =-1;
						idEnd =-1;
						for (int j=0;j<nodeLst.size();j++)
						{
							if(l.getStart() == nodeLst.get(j))
							{
								idStart =j;
							}
							if(l.getEnd() == nodeLst.get(j))
							{
								idEnd =j;
							}
							if(idStart!=-1 && idEnd !=-1)
								break;
						}
						if(idStart==-1 && idEnd==-1)
						{
							//add canh Z1.get(i1) den Z2.get(i)
							idStart=Z1.indexOf(l.getStart());
							idEnd = Z2.indexOf(l.getEnd());
							if(idStart!=-1 && idEnd!=-1)
							{
								if(l.getStart()==l.getEnd())
								{
									edgeLst.add(new WeitEdge(node1+idStart+1, idEnd+node2+1, 10.0));
								}
								else
									if(_g.getEdgeWeight(l.getStart(), l.getEnd())>=_d.getBw())
									//if(_g.getEdgeWeight(l.getStart(), l.getEnd())>0)
										edgeLst.add(new WeitEdge(node1+idStart+1, idEnd+node2+1, _g.getEdgeWeight(l.getStart(), l.getEnd())));
							}
							
						}
						else
						{
							if(idStart==-1)
							{
								//add canh bat dau tu Z1.get(i1)
								idStart=Z1.indexOf(l.getStart());
								if(idStart!=-1)
								{
									if(_g.getEdgeWeight(l.getStart(), l.getEnd())>=_d.getBw())
									//if(_g.getEdgeWeight(l.getStart(), l.getEnd())>0)
										edgeLst.add(new WeitEdge(node1+idStart+1, idEnd+lastNode+1, _g.getEdgeWeight(l.getStart(), l.getEnd())));
								}
								continue;
							}
							if(idEnd==-1)
							{
								idEnd = Z2.indexOf(l.getEnd());
								if(idEnd!=-1&& _g.getEdgeWeight(l.getStart(), l.getEnd())>=_d.getBw())
								//if(idEnd!=-1&& _g.getEdgeWeight(l.getStart(), l.getEnd())>0)
									edgeLst.add(new WeitEdge(idStart+lastNode+1, idEnd+node2+1, _g.getEdgeWeight(l.getStart(), l.getEnd())));
								continue;
							}
							if(l.getStart()==l.getEnd())
							{
								edgeLst.add(new WeitEdge(idStart+lastNode+1,idEnd+lastNode+1, 10.0));
							}
							else
								//if(idEnd!=-1&& _g.getEdgeWeight(l.getStart(), l.getEnd())>0)
								if(idEnd!=-1&& _g.getEdgeWeight(l.getStart(), l.getEnd())>=_d.getBw())
									edgeLst.add(new WeitEdge(idStart+lastNode+1,idEnd+lastNode+1, _g.getEdgeWeight(l.getStart(), l.getEnd())));
							
						}						
					}
				}
				
			}
		}
		nGraph g_save = new nGraph(NumV);
		
		System.out.println("Number of Extended Link: "+edgeLst.size());
		if(edgeLst.size()==0)
			return null;
        for (WeitEdge edges : edgeLst) {
        	int s = edges.getO();
        	int t = edges.getD();
			double w= edges.getW();
			g_save.setEdgeWeight(s, t, w);
		}
	   	for (int i=0;i<g_save.getV();i++)
       {
	   		g_save.setCap(i+1, k.get(i));
       }    
	   	//noVertex = g_save.getV();
	   	edgeLst =null;
	   	
		
		return g_save;
		
	
	}
	public static ArrayList<ArrayList<Integer>> shortestPath_new(nGraph _g, nDemand _d,double[][][] _w)
	{
		int _v= _g.getV();
		double proReq= _d.getProcessReq();
		double bw= _d.getBw();
		ArrayList<Integer> fLst = _d.getFunctions();
		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		source = _d.getSrc();
		destination = _v* (fLst.size()) + _d.getDest();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
		DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g_i = new DefaultDirectedWeightedGraph<>(DefaultWeightedEdge.class);
		List<Vertex> vertexList = new ArrayList<Vertex>();
		int noVer=0;
		ArrayList<Integer> nodeLst = new ArrayList<>();
		
		for (int k=0;k<fLst.size()+1;k++)
		{
			for (int i = 0; i < _v; i++) 
			{
				int s= noVer + i+1;
				Vertex v = new Vertex(s);
				vertexList.add(v);
				g_i.addVertex(v);
				nodeLst.add(i+1);
			}
			noVer+=_v;
		}
		int lastNode=0;
		for (int i=0;i<fLst.size()+1;i++)
		{
			for (int j1=0;j1<_v;j1++)
				for(int j2=0;j2<_v;j2++)
				{
					if((j1!=j2) && (_w[j1][j2][i]>0))
					{
						Vertex v1 = vertexList.get(lastNode+j1);
						Vertex v2 = vertexList.get(lastNode+j2);
						DefaultWeightedEdge e = g_i.addEdge(v1, v2);
						g_i.setEdgeWeight(e,_w[j1][j2][i]);
					}
				}
			lastNode+=_v;
		}
		
		//add link =0;
		lastNode =0;
		for (int i=0;i<fLst.size();i++)
		{
			
			ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
			for(int j=0;j<Zi.size();j++)
			{					
				int node = Zi.get(j);
				if(_w[node-1][node-1][i]!=-1.0)
				{
					Vertex v1 = vertexList.get(lastNode+node-1);
					Vertex v2 = vertexList.get(lastNode+_v+node -1);
					DefaultWeightedEdge e = g_i.addEdge(v1, v2);
					g_i.setEdgeWeight(e,_w[node-1][node-1][i]);
				}
			}
			lastNode += _v;
		}
		
		//System.out.println("src: "+ src);
		DijkstraMinh d = new DijkstraMinh(g_i);
		
		d.computeAllShortestPaths(source);
		//Collection<Vertex> vertices = g_i.getVertices();
		Vertex v= vertexList.get(0);
		for (Vertex ve:vertexList)
		{
			if (ve.getId()==destination)
			{
				v=ve;
				break;
			}
		}
		int i = 1;
		boolean check=false;
					
		Set<List<Vertex>> allShortestPaths = d.getAllShortestPathsTo(v);
 
		for (Iterator<List<Vertex>> iter = allShortestPaths.iterator(); iter.hasNext(); i++)
		{
			check=false;
			_shortestPath = new ArrayList<>();
			List<Vertex> p = (List<Vertex>) iter.next();
			if(!check && p.get(0).getId()==source)
			{
				
				for (Vertex v1:p)
				{
					_shortestPath.add(v1.getId());
				}
				_shortestPathLst.add(_shortestPath);
				//System.out.println("Path " + i + ": " + p);
			}
		}
		
		if(_shortestPathLst.size()==0)
			return null;

		return _shortestPathLst;
	
	}
	public static ArrayList<ArrayList<Integer>> shortestPath(nGraph _g, nDemand _d,double[][][] _w, ArrayList<Node> combNode)
	{
		ArrayList<ArrayList<Node>> allComb = new ArrayList<>();
		
		int numberofGraph = 1;
		for (Node n: combNode)
		{
			int noComb = n.getvSetComb().size();
			
			numberofGraph = numberofGraph * noComb;
			if(numberofGraph>5)
			{
				numberofGraph = numberofGraph/noComb;
				break;
			}
			
		}
		for (int i=0;i<numberofGraph;i++)
		{
			allComb.add(combNode);
		}
		

		for (int i=0;i<combNode.size();i++)
		{
			int id =0;
			for (int j=0;j<numberofGraph;j++)
			{
				ArrayList<Node> lst = allComb.get(j);
				Node n = lst.get(i);
				if(id<n.getvSetComb().size())
				{
					n.setvSetLst(n.getvSetComb().get(id));
					id ++;						
				}
				else
				{
					id =0;
					n.setvSetLst(n.getvSetComb().get(id));
					id++;
				}
				lst.set(i,n);
				
			}
		}
		int _v= _g.getV();
		double proReq= _d.getProcessReq();
		double bw= _d.getBw();
		ArrayList<Integer> fLst = _d.getFunctions();
		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		ArrayList<Node> funcNode = new ArrayList<>();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
		List<Vertex> vertexList = new ArrayList<Vertex>();
		ArrayList<Integer> nodeLst = new ArrayList<>();
		source = _d.getSrc();
		destination = _v* (fLst.size()) + _d.getDest();
		for(int noG=0;noG<numberofGraph;noG++)
		{	
			funcNode = allComb.get(noG);
			_shortestPath = new ArrayList<>();
			DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g_i = new DefaultDirectedWeightedGraph<>(DefaultWeightedEdge.class);
			vertexList = new ArrayList<Vertex>();
			int noVer=0;
			nodeLst = new ArrayList<>();
			
			for (int k=0;k<fLst.size()+1;k++)
			{
				for (int i = 0; i < _v; i++) 
				{
					int s= noVer + i+1;
					Vertex v = new Vertex(s);
					vertexList.add(v);
					g_i.addVertex(v);
					nodeLst.add(i+1);
				}
				noVer+=_v;
			}
			int lastNode=0;
			for (int i=0;i<fLst.size()+1;i++)
			{
				for (int j1=0;j1<_v;j1++)
					for(int j2=0;j2<_v;j2++)
					{
						if((j1!=j2) && (_w[j1][j2][i]>0))
						{
							Vertex v1 = vertexList.get(lastNode+j1);
							Vertex v2 = vertexList.get(lastNode+j2);
							DefaultWeightedEdge e = g_i.addEdge(v1, v2);
							g_i.setEdgeWeight(e,_w[j1][j2][i]);
						}
					}
				lastNode+=_v;
			}
			
			//add link =0;
			lastNode =0;
			for (int i=0;i<fLst.size();i++)
			{
				
				ArrayList<Integer> Zi= getFunction(fLst.get(i)).getVnfNode();
				for(int j=0;j<Zi.size();j++)
				{					
					int node = Zi.get(j);
					if(_w[node-1][node-1][i]!=-1.0)
					{
						
						for (int nodeId =0;nodeId<funcNode.size();nodeId++)
						{
							if(funcNode.get(nodeId).getid()==node)
							{
								if(funcNode.get(nodeId).getvSetLst().contains(i))
								{
									Vertex v1 = vertexList.get(lastNode+node-1);
									Vertex v2 = vertexList.get(lastNode+_v+node -1);
									DefaultWeightedEdge e = g_i.addEdge(v1, v2);
									g_i.setEdgeWeight(e,_w[node-1][node-1][i]);
								}
								break;
							}
						}
					}
				}
				lastNode += _v;
			}
			
			//System.out.println("src: "+ src);
			DijkstraMinh d = new DijkstraMinh(g_i);
			
			d.computeAllShortestPaths(source);
			//Collection<Vertex> vertices = g_i.getVertices();
			Vertex v= vertexList.get(0);
			for (Vertex ve:vertexList)
			{
				if (ve.getId()==destination)
				{
					v=ve;
					break;
				}
			}
			int i = 1;
			boolean check=false;
						
			Set<List<Vertex>> allShortestPaths = d.getAllShortestPathsTo(v);
	 
			for (Iterator<List<Vertex>> iter = allShortestPaths.iterator(); iter.hasNext(); i++)
			{
				check=false;
				_shortestPath = new ArrayList<>();
				List<Vertex> p = (List<Vertex>) iter.next();
				if(!check && p.get(0).getId()==source)
				{
					
					for (Vertex v1:p)
					{
						_shortestPath.add(v1.getId());
					}
					_shortestPathLst.add(_shortestPath);
					//System.out.println("Path " + i + ": " + p);
				}
			}
		}
		
		
		if(_shortestPathLst.size()==0)
			return null;

		return _shortestPathLst;
	}
	public static ArrayList<ArrayList<Integer>> SP(int src,int dest,nGraph _g)
	{

		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
	DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g_i = new DefaultDirectedWeightedGraph<>(DefaultWeightedEdge.class);
		List<Vertex> vertexList = new ArrayList<Vertex>();
		for (int i = 0; i < _g.getV(); i++) {
				int s= i+1;
				Vertex v = new Vertex(s);
				vertexList.add(v);
				g_i.addVertex(v);
		}
		for (int j=0;j<vertexList.size();j++)
        {	        	
        	for(int k=0;k<vertexList.size();k++)
        	{
        			if(j!=k&&_g.getEdgeWeight(vertexList.get(j).getId(), vertexList.get(k).getId())>0)
        			{
        			
        				DefaultWeightedEdge e = g_i.addEdge(vertexList.get(j), vertexList.get(k));
        				g_i.setEdgeWeight(e, 1.0);
        			}
        	}
        } 
		//System.out.println("src: "+ src);
		DijkstraMinh d = new DijkstraMinh(g_i);
		
		d.computeAllShortestPaths(src);
		//Collection<Vertex> vertices = g_i.getVertices();
		Vertex v= vertexList.get(0);
		for (Vertex _v:vertexList)
		{
			if (_v.getId()==dest)
			{
				v=_v;
				break;
			}
		}
		int i = 1;
		boolean check=false;
			Set<List<Vertex>> allShortestPaths = d.getAllShortestPathsTo(v);
 
			for (Iterator<List<Vertex>> iter = allShortestPaths.iterator(); iter.hasNext(); i++)
			{
				check=false;
				_shortestPath = new ArrayList<>();
				List<Vertex> p = (List<Vertex>) iter.next();
				if(!check && p.get(0).getId()==src)
				{
					
					for (Vertex v1:p)
					{
						_shortestPath.add(v1.getId());
					}
					_shortestPathLst.add(_shortestPath);
				}
			}
		if(_shortestPathLst.size()==0)
			return null;
		return _shortestPathLst;
	
	
	}
	
	public static ArrayList<Integer> SP_GreedyForward(int src, ArrayList<Integer> destLst,nGraph _g, double maxBw,double maxReq)
	{
		ArrayList<Integer> _shortestPath = new ArrayList<>();
		DirectedGraph<Vertex, DefaultEdge> g_i = new DefaultDirectedGraph<>(DefaultEdge.class);
		List<Vertex> vertexList = new ArrayList<Vertex>();
		for (int i = 0; i < _g.getV(); i++) {
				int s= i+1;
				Vertex v = new Vertex(s);
				vertexList.add(v);
				g_i.addVertex(v);
		}
		for (int j=0;j<vertexList.size();j++)
        {	        	
        	for(int k=0;k<vertexList.size();k++)
        	{
        		if(_g.getCap(vertexList.get(j).getId())>=maxReq && _g.getCap(vertexList.get(k).getId())>=maxReq)
        		{
        			if(j!=k&&_g.getEdgeWeight(vertexList.get(j).getId(), vertexList.get(k).getId())>= maxBw)
        			{
        			
        				g_i.addEdge(vertexList.get(j), vertexList.get(k));
        			}
        		}
        	}
        } 
		FloydWarshallShortestPaths<Vertex, DefaultEdge> floyd = new FloydWarshallShortestPaths<>(g_i);
		List<GraphPath<Vertex,DefaultEdge>> allPaths = floyd.getShortestPaths(vertexList.get(src-1));
		int min= Integer.MAX_VALUE;
		for(GraphPath<Vertex,DefaultEdge> _p:allPaths)
		{			
			Vertex destination = _p.getEndVertex();
			if(destLst.contains(destination.getId()))
			{
				List<DefaultEdge> vLst = _p.getEdgeList();
				
				if(vLst.size()<min)
				{
					min= vLst.size();
					//luu vao _shortestPath
					_shortestPath = new ArrayList<>();
					for(DefaultEdge e:vLst)
					{
						_shortestPath.add(g_i.getEdgeSource(e).getId());
					}
					_shortestPath.add(_p.getEndVertex().getId());
				}
			}
		}	
		if (_shortestPath.size()==0)
			return null;
	return _shortestPath;
	
	}
	public static ArrayList<ArrayList<Integer>> shortestPaths (int src, int dest,nGraph _g, double maxBw,double maxReq)
	{
		ArrayList<ArrayList<Integer>> _shortestPathLst = new ArrayList<>();
		ArrayList<Integer> _shortestPath = new ArrayList<>();
	DefaultDirectedWeightedGraph<Vertex, DefaultWeightedEdge> g_i = new DefaultDirectedWeightedGraph<>(DefaultWeightedEdge.class);
		List<Vertex> vertexList = new ArrayList<Vertex>();
		for (int i = 0; i < _g.getV(); i++) {
				int s= i+1;
				Vertex v = new Vertex(s);
				vertexList.add(v);
				g_i.addVertex(v);
		}
		for (int j=0;j<vertexList.size();j++)
        {	        	
        	for(int k=0;k<vertexList.size();k++)
        	{
        		if(_g.getCap(vertexList.get(j).getId())>=maxReq && _g.getCap(vertexList.get(k).getId())>=maxReq)
        		{
        			if(j!=k&&_g.getEdgeWeight(vertexList.get(j).getId(), vertexList.get(k).getId())>= maxBw)
        			{
        			
        				DefaultWeightedEdge e = g_i.addEdge(vertexList.get(j), vertexList.get(k));
        				if(_g.getEdgeWeight(vertexList.get(j).getId(), vertexList.get(k).getId()) ==100.0)
        					g_i.setEdgeWeight(e,0.0);
        				else
        					g_i.setEdgeWeight(e, 1.0);
        			}
        		}
        	}
        } 
		//System.out.println("src: "+ src);
		DijkstraMinh d = new DijkstraMinh(g_i);
		
		d.computeAllShortestPaths(src);
		//Collection<Vertex> vertices = g_i.getVertices();
		Vertex v= vertexList.get(0);
		for (Vertex _v:vertexList)
		{
			if (_v.getId()==dest)
			{
				v=_v;
				break;
			}
		}
		int i = 1;
		boolean check=false;
		
//		for (Iterator<Vertex> iterator = vertices.iterator(); iterator.hasNext();) {
//			v = (Vertex) iterator.next();
//			if(v.getId()!=dest)
//				continue;			
			Set<List<Vertex>> allShortestPaths = d.getAllShortestPathsTo(v);
 
			for (Iterator<List<Vertex>> iter = allShortestPaths.iterator(); iter.hasNext(); i++)
			{
				check=false;
				_shortestPath = new ArrayList<>();
				List<Vertex> p = (List<Vertex>) iter.next();
//				for(int j=0;j<p.size()-1;j++)
//				{
//					if(_g.getEdgeWeight(p.get(j).getId(), p.get(j+1).getId())==0)
//					{
//						check=true;
//						break;
//					}
//				}
				if(!check && p.get(0).getId()==src)
				{
					
					for (Vertex v1:p)
					{
						_shortestPath.add(v1.getId());
					}
					_shortestPathLst.add(_shortestPath);
					//System.out.println("Path " + i + ": " + p);
				}
			}
//			i = 1;
//			break;
//		} 
		if(_shortestPathLst.size()==0)
			return null;
		return _shortestPathLst;
	
	}
	public static nGraph prunedNetwork(nDemand _d, nGraph _g)
	{
		double proReq = _d.getProcessReq();
		double bw = _d.getBw();
		Vector<Double> _cap=new Vector<>();
		List<List<Double>> _w = new ArrayList<>();
		
		for (int i=0;i<_g.getV();i++)
		{
			_cap.add(_g.getCap(i+1));			
		}
		ArrayList<Double> temp=new ArrayList<>();
		for (int i=0;i<_g.getV();i++)
		{
			temp=new ArrayList<>();
			for(int j=0;j<_g.getV();j++)
			{
				
				if((i!=j)&&(_g.getCap(i+1)>=proReq)&&(_g.getCap(j+1)>=proReq)&&(_g.getEdgeWeight(i+1, j+1)>=bw))
				{
					temp.add(_g.getEdgeWeight(i+1, j+1));
				}
				else
					temp.add(0.0);
			}
			_w.add(temp);
		}	
		
		nGraph g_new = new nGraph(_cap,_w);
		return g_new;
	}
	public static boolean CheckFeasible(ArrayList<Integer> _p, nGraph _g,nDemand _d)
	{
		double bw = _d.getBw();
		double req = _d.getProcessReq();
		nGraph g_tamp = new nGraph(_g.cap, _g.w);
		
		for (int i=0;i<_p.size()-1;i++)
		{
			int _srcNode = _p.get(i);
			int _destNode = _p.get(i+1);
			double _w = g_tamp.getEdgeWeight(_srcNode, _destNode)-bw;
			double c_temp= Math.round(100000 *_w)/100000.0 ;
			if(c_temp<0)
			{
				return false;
			}
			else
				g_tamp.setEdgeWeight(_srcNode, _destNode, c_temp);
				
		}
		
		for(int i = 0;i<_p.size();i++)
		{
			int _node = _p.get(i);
			double _c= g_tamp.getCap(_node) - req;
			double c_temp= Math.round(100000 *_c)/100000.0 ;
			if(c_temp<0)
			{
				return false;
			}
			else
			{
				g_tamp.setCap(_node, c_temp);
			}
		}
		
		for(int i = 0; i< funLoc.size();i++)
		{
			Pair _pair = funLoc.get(i);
			int _node = _pair.getnode();
			int _func = _pair.getfunction();
			double _c = g_tamp.getCap(_node) - getFunction(_func).getLamda();
			double c_temp= Math.round(100000 *_c)/100000.0 ;
			if(c_temp<0)
				return false;
			else
				g_tamp.setCap(_node, c_temp);
						
		}
		return true;
	}
	
	public static ArrayList<Integer> convertPath(ArrayList<Integer> _p,nDemand _d,nGraph _g)
	{
		copyLinks = null;
		copyLinks= new ArrayList<>();
		ArrayList<Pair> _tempLinks = new ArrayList<>();
		funLoc= new ArrayList<>();
		int lastnode=0;
		int _v = _g.getV();
		ArrayList<Integer> p_final = new ArrayList<>();
		int _idFunction=0;
		int start=-1,end=-1;
		for(int j=0;j<_p.size()-1;j++)
		{
			start = _p.get(j)-lastnode;
			end= _p.get(j+1)-lastnode;
			if(end< _v+1)
			{
				p_final.add(start);
				_tempLinks.add(new Pair(start, end));
			}
			else
			{
				funLoc.add(new Pair(start, _d.getFunctions().get(_idFunction)));
				lastnode+=_v;
				_idFunction++;
				_tempLinks.add(new Pair(start, start));
				copyLinks.add(_tempLinks);
				_tempLinks = new ArrayList<>();
			}
		}
		
		start = _p.get(_p.size()-1)-lastnode;
		if(end>_v)
			end = end -_v;
		if(end==start)
			{
				if(_tempLinks.size()==0)
					_tempLinks.add(new Pair(end,start));
			}
		else
			_tempLinks.add(new Pair(end,start));
		copyLinks.add(_tempLinks);
		p_final.add(start);
		return p_final;
		
	}
	public static ArrayList<Integer> B_2Fake(nDemand _d,nGraph _g,double delPar)
	{



		fl=true;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_g = new double[para_V][para_V];
		double[] var_h = new double[para_V];
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							para_w[i][j][k]= 1.0;
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							//cap nho nhat la 0.15 
							
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= 0.0;
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}		
		
			
			ArrayList<ArrayList<Integer>> xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=0;
						//p_final = convertPath(p, _d, _g);
						return p_final;
					}
						
				}
			}	
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
					var_g[i][j]=-para_C[i][j];
			for (int i=0;i<para_V;i++)
				var_h[i]=-para_bigP[i];
			int id = UtilizeFunction.randInt(0, xLst.size()-1);
			ArrayList<Integer> _p= xLst.get(id);
			int lastnode =0;
			int _v = g_prune.getV();
			int _idFunction=0;
			for(int j=0;j<_p.size()-1;j++)
			{
				int start = _p.get(j)-lastnode;
				int end= _p.get(j+1)-lastnode;
				if(end< _v+1)
				{
					var_g[start-1][end-1]+=para_b;
					var_h[start-1]+= para_p;
					var_x[start-1][end-1][_idFunction]=1.0;
				}
				else
				{
//					if(j<_p.size()-2 && (_p.get(j+2)>(_idFunction+2)*_v))
//						var_h[start-1]+= para_p;
					var_h[start-1]+=para_q[_idFunction];
					var_x[start-1][start-1][_idFunction]=1.0;
					lastnode+=_v;
					_idFunction++;	
				}
			}
			int start= _p.get(_p.size()-1)-lastnode;
			var_h[start-1]+= para_p;
		
		int k_iter=0;
		int Max_iter = 1;
		while(k_iter<Max_iter)
		{
			k_iter++;	
			
			//lua chon alpha
			//double al = a/(Math.sqrt(k_iter));	
		
			Double delta = 0.0;
			Double _mau =0.0;
			Double _tu = 0.0;
			double t=0.0;
			double tong=0.0;
			
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
				{
					for (int k=0;k<para_noF+1;k++)
					{
						if (i!=j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_g[i][j]>0)
								{
									tong++;
									_mau+=para_b* var_g[i][j];
								}
								if(var_h[j]>0)
									_mau+=para_p *var_h[j];
									
							}
						}
						else
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_h[i]>0)
								{
									tong++;
									_mau+=para_q[k] *var_h[i];
								}
									
							}							
						}
					}
						
				}
			
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
				{
					t=0.0;
					for (int k=0;k<para_noF+1;k++)
					{
						if (i!=j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_g[i][j]>0)
								{
									t +=para_C[i][j]/para_b;
									break;
								}
									
							}
						}
					}
					for (int k=0;k<para_noF+1;k++)
					{
						if (i==j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_h[i]>0)
								{
									t +=(para_bigP[i]-para_p)/para_q[k];
									break;
								}
									
							}							
						}
					}
					if(_tu<t)
						_tu = t;
						
				}
			
			delta = tong-_tu;
			if(delta<1)
				delta=1.0;
			delta = delPar;
			delta = delta/_mau;
				
			int alphaIter = delta.intValue()+1;
			
			
			//thu
			//alphaIter =1;
			
			//sudung Equation (6)
			
			for (int i=0;i<para_V;i++)
				for(int j=0;j<para_V;j++)
				{
					if(i!=j)
					{
						var_gama[i][j] = var_gama[i][j] + alphaIter * var_g[i][j]; 
						if(var_gama[i][j]<=0)
							var_gama[i][j]=0.0;
					}
					
				}
			
			for(int i=0;i<para_V;i++)
			{
				var_mu[i] = var_mu[i] + alphaIter * var_h[i]; 
				if(var_mu[i]<=0)
					var_mu[i]=0.0;
			}
			
			for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					//double randNo = UtilizeFunction.randDouble(0, 1);
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
//							if(para_w[i][j][k]!=1)
//								System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
								
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
							{
								para_w[i][j][k]= para_q[k]* var_mu[i];
//								if(para_w[i][j][k]!=0)
//									System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
							}
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}
			
			xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst!=null && xLst.size()>0)
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=3;
						//p_final = convertPath(p, _d, _g);
//						System.out.println("good length: "+ p_final.size());
						return p_final;
					}
				}
			}					
			//xet tung duong di
//			for (Double[][][] x_temp : xLst)
//			{
//				var_x = x_temp;
//				
//			}
			
			
			
		}
		flag =2;
		return null;
	
	
	
	}
	public static ArrayList<Integer> B_2(nDemand _d, nGraph _g,double delPar)
	{


		fl=true;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_g = new double[para_V][para_V];
		double[] var_h = new double[para_V];
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							//para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
							para_w[i][j][k]= para_b/para_C[i][j];
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							//cap nho nhat la 0.15 
							
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= 0.1/_g.getCap(i+1);
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}		
		
			
			ArrayList<ArrayList<Integer>> xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=0;
						//p_final = convertPath(p, _d, _g);
						return p_final;
					}
						
				}
			}	
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
					var_g[i][j]=-para_C[i][j];
			for (int i=0;i<para_V;i++)
				var_h[i]=-para_bigP[i];
			int id = UtilizeFunction.randInt(0, xLst.size()-1);
			ArrayList<Integer> _p= xLst.get(id);
			int lastnode =0;
			int _v = g_prune.getV();
			int _idFunction=0;
			for(int j=0;j<_p.size()-1;j++)
			{
				int start = _p.get(j)-lastnode;
				int end= _p.get(j+1)-lastnode;
				if(end< _v+1)
				{
					var_g[start-1][end-1]+=para_b;
					var_h[start-1]+= para_p;
					var_x[start-1][end-1][_idFunction]=1.0;
				}
				else
				{
//					if(j<_p.size()-2 && (_p.get(j+2)>(_idFunction+2)*_v))
//						var_h[start-1]+= para_p;
					var_h[start-1]+=para_q[_idFunction];
					var_x[start-1][start-1][_idFunction]=1.0;
					lastnode+=_v;
					_idFunction++;	
				}
			}
			int start= _p.get(_p.size()-1)-lastnode;
			var_h[start-1]+= para_p;
		
		int k_iter=0;
		int Max_iter = 1;
		while(k_iter<Max_iter)
		{
			k_iter++;	
			
			//lua chon alpha
			//double al = a/(Math.sqrt(k_iter));	
		
			Double delta = 0.0;
			Double _mau =0.0;
			Double _tu = 0.0;
			double t=0.0;
			double tong=0.0;
			
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
				{
					for (int k=0;k<para_noF+1;k++)
					{
						if (i!=j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_g[i][j]>0)
								{
									tong++;
									_mau+=para_b* var_g[i][j];
								}
								if(var_h[j]>0)
									_mau+=para_p *var_h[j];
									
							}
						}
						else
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_h[i]>0)
								{
									tong++;
									_mau+=para_q[k] *var_h[i];
								}
									
							}							
						}
					}
						
				}
			
			for (int i=0;i<para_V;i++)
				for (int j=0;j<para_V;j++)
				{
					t=0.0;
					for (int k=0;k<para_noF+1;k++)
					{
						if (i!=j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_g[i][j]>0)
								{
									t +=para_C[i][j]/para_b;
									break;
								}
									
							}
						}
					}
					for (int k=0;k<para_noF+1;k++)
					{
						if (i==j )
						{
							if(var_x[i][j][k]==1.0)
							{
								if(var_h[i]>0)
								{
									t +=(para_bigP[i]-para_p)/para_q[k];
									break;
								}
									
							}							
						}
					}
					if(_tu<t)
						_tu = t;
						
				}
			
			delta = tong-_tu;
			if(delta<1)
				delta=1.0;
			delta = delPar;
			delta = delta/_mau;
				
			int alphaIter = delta.intValue()+1;
			
			
			//thu
			//alphaIter =1;
			
			//sudung Equation (6)
			
			for (int i=0;i<para_V;i++)
				for(int j=0;j<para_V;j++)
				{
					if(i!=j)
					{
						var_gama[i][j] = var_gama[i][j] + alphaIter * var_g[i][j]; 
						if(var_gama[i][j]<=0)
							var_gama[i][j]=0.0;
					}
					
				}
			
			for(int i=0;i<para_V;i++)
			{
				var_mu[i] = var_mu[i] + alphaIter * var_h[i]; 
				if(var_mu[i]<=0)
					var_mu[i]=0.0;
			}
			
			for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					//double randNo = UtilizeFunction.randDouble(0, 1);
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
//							if(para_w[i][j][k]!=1)
//								System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
								
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
							{
								para_w[i][j][k]= para_q[k]* var_mu[i];
//								if(para_w[i][j][k]!=0)
//									System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
							}
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}
			
			xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst!=null && xLst.size()>0)
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=3;
						//p_final = convertPath(p, _d, _g);
						//System.out.println("good length: "+ p_final.size());
						return p_final;
					}
				}
			}					
			//xet tung duong di
//			for (Double[][][] x_temp : xLst)
//			{
//				var_x = x_temp;
//				
//			}
			
			
			
		}
		flag =2;
		return null;
	
	
	}
	public static ArrayList<Integer> B_1Fake(nDemand _d,nGraph _g)
	{


		fl=true;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							para_w[i][j][k]= 1.0;
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							//cap nho nhat la 0.15 
							
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= 0.0;
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}		
		
			
			ArrayList<ArrayList<Integer>> xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=0;
						
						return p_final;
					}
				}
			}
		flag =2;
		return null;
	
	
	}
	
	public static ArrayList<Integer> B_1(nDemand _d,nGraph _g)
	{

		fl=true;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							//para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
							para_w[i][j][k]= para_b/para_C[i][j];
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							//cap nho nhat la 0.15 
							
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= 0.1/_g.getCap(i+1);
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}		
		
			
			ArrayList<ArrayList<Integer>> xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					if (isFeasible)
					{
						flag=0;
						//p_final = convertPath(p, _d, _g);
						return p_final;
					}
				}
			}
		flag =2;
		return null;
	
	}
	public static ArrayList<Integer> A_2(nDemand _d, nGraph _g)
	{

		fl=true;
		double a=0.5;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_g = new double[para_V][para_V];
		double[] var_h = new double[para_V];
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
							para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= para_q[k]* var_mu[i];
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}
		
		ArrayList<Node> funcNode = new ArrayList<>();
		for (int k=0;k<para_noF;k++)
		{
			ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
			for (int i:Z_i)
			{
				if(_g.getCap(i)>=para_p + para_q[k])
				{
					boolean nodeFlag= false;
					Node n = new Node(i);
					for (Node fN : funcNode)
					{
						if (n.CompareTo(fN))
						{
							nodeFlag =true;
							fN.setusedNo(fN.getusedNo()+1);
							ArrayList<Integer> tempArr = fN.getvSetLst();
							tempArr.add(k);
							fN.setvSetLst(tempArr);
							break;
						}
					}
					if(!nodeFlag)
					{
						n.setusedNo(1);
						ArrayList<Integer> tempArr = new ArrayList<>();
						tempArr.add(k);
						n.setvSetLst(tempArr);
						n.setReq(g_prune.getCap(i));
						funcNode.add(n);
					}
				}
			}
			
			
			
		}
		
		//set combination for each node nay
		ArrayList<ArrayList<Integer>> combLst= new ArrayList<>();
		for (int j =0;j< funcNode.size();j++)
		{
			Node node = funcNode.get(j);
			
			Double t = (node.getReq()-para_p)/para_q[0];
			int noNode = t.intValue();
			combLst = new ArrayList<>();
			
			int noLst = node.getvSetLst().size();
			ArrayList<Integer> _vLst = node.getvSetLst();
			if(noNode < noLst)
			{
				combinations(noNode, _vLst, combLst);
			}
			else
			{
				
				combLst.add(_vLst);
				
			}	
			node.setvSetComb(combLst);
			_vLst= null;
			combLst = null;
		}		
		
			ArrayList<ArrayList<Integer>> xLst = shortestPath(g_prune, _d, para_w,funcNode);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					
					p_final = convertPath(p, _d, _g);
					
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					
					
					if (isFeasible)
					{
						flag=0;
						//p_final = convertPath(p, _d, _g);
						return p_final;
					}
				}
			}
//			for (int i=0;i<para_V;i++)
//				for (int j=0;j<para_V;j++)
//					var_g[i][j]=-para_C[i][j];
//			for (int i=0;i<para_V;i++)
//				var_h[i]=-para_bigP[i];
//			int id = UtilizeFunction.randInt(0, xLst.size()-1);
//			ArrayList<Integer> _p= xLst.get(id);
//			int lastnode =0;
//			int _v = g_prune.getV();
//			int _idFunction=0;
//			for(int j=0;j<_p.size()-1;j++)
//			{
//				int start = _p.get(j)-lastnode;
//				int end= _p.get(j+1)-lastnode;
//				if(end< _v+1)
//				{
//					var_g[start-1][end-1]+=para_b;
//					var_h[start-1]+= para_p;
//					var_x[start-1][end-1][_idFunction]=1.0;
//				}
//				else
//				{
////					if(j<_p.size()-2 && (_p.get(j+2)>(_idFunction+2)*_v))
////						var_h[start-1]+= para_p;
//					var_h[start-1]+=para_q[_idFunction];
//					var_x[start-1][start-1][_idFunction]=1.0;
//					lastnode+=_v;
//					_idFunction++;	
//				}
//			}
//			int start= _p.get(_p.size()-1)-lastnode;
//			var_h[start-1]+= para_p;
//		
//		int k_iter=0;
//		int Max_iter = 1;
//		while(k_iter<Max_iter)
//		{
//			k_iter++;
//			
//			//tinh w(i,j,k) for do thi prunk
//					
////			
////			for (int i=0;i<para_V;i++)
////				for (int j=0;j<para_V;j++)
////					for (int k=0;k<para_noF+1;k++)
////					{
////						if (i!=j )
////						{
////							if(para_C[i][j]>=para_b)
////							{
////								para_w[i][j][k]= 1 + alphaIter * var_g[i][j];
//////								if(para_w[i][j][k]!=1)
//////									System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
////									
////							}
////							else
////								para_w[i][j][k]= -1.0;
////						}
////						else
////						{
////							if(k<para_noF)
////							{
////								ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
////								if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
////								{
////									para_w[i][j][k]= alphaIter * var_h[i];
//////									if(para_w[i][j][k]!=0)
//////										System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
////								}
////								else
////									para_w[i][j][k] = -1.0;
////							}
////							else
////								para_w[i][j][k] = -1.0;
////							
////						}
////					}
////				
//			
//			
//			
//			//lua chon alpha
//			//double al = a/(Math.sqrt(k_iter));	
//		
//			Double delta = 0.0;
//			Double _mau =0.0;
//			Double _tu = 0.0;
//			double t=0.0;
//			double tong=0.0;
//			
//			for (int i=0;i<para_V;i++)
//				for (int j=0;j<para_V;j++)
//				{
//					for (int k=0;k<para_noF+1;k++)
//					{
//						if (i!=j )
//						{
//							if(var_x[i][j][k]==1.0)
//							{
//								if(var_g[i][j]>0)
//								{
//									tong++;
//									_mau+=para_b* var_g[i][j];
//								}
//								if(var_h[j]>0)
//									_mau+=para_p *var_h[j];
//									
//							}
//						}
//						else
//						{
//							if(var_x[i][j][k]==1.0)
//							{
//								if(var_h[i]>0)
//								{
//									tong++;
//									_mau+=para_q[k] *var_h[i];
//								}
//									
//							}							
//						}
//					}
//						
//				}
//			
//			for (int i=0;i<para_V;i++)
//				for (int j=0;j<para_V;j++)
//				{
//					t=0.0;
//					for (int k=0;k<para_noF+1;k++)
//					{
//						if (i!=j )
//						{
//							if(var_x[i][j][k]==1.0)
//							{
//								if(var_g[i][j]>0)
//								{
//									t +=para_C[i][j]/para_b;
//									break;
//								}
//									
//							}
//						}
//					}
//					for (int k=0;k<para_noF+1;k++)
//					{
//						if (i==j )
//						{
//							if(var_x[i][j][k]==1.0)
//							{
//								if(var_h[i]>0)
//								{
//									t +=(para_bigP[i]-para_p)/para_q[k];
//									break;
//								}
//									
//							}							
//						}
//					}
//					if(_tu<t)
//						_tu = t;
//						
//				}
//			
//			delta = tong-_tu;
//			if(delta<1)
//				delta=1.0;
//			delta = delta/_mau;
//				
//			int alphaIter = delta.intValue()+1;
//			//sudung Equation (6)
//			
//			for (int i=0;i<para_V;i++)
//				for(int j=0;j<para_V;j++)
//				{
//					if(i!=j)
//					{
//						var_gama[i][j] = var_gama[i][j] + alphaIter * var_g[i][j]; 
//						if(var_gama[i][j]<=0)
//							var_gama[i][j]=0.0;
//					}
//					
//				}
//			
//			for(int i=0;i<para_V;i++)
//			{
//				var_mu[i] = var_mu[i] + alphaIter * var_h[i]; 
//				if(var_mu[i]<=0)
//					var_mu[i]=0.0;
//			}
//			
//			for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//				{
//					if (i!=j )
//					{
//						if(para_C[i][j]>=para_b)
//						{
//							para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
//							if(para_w[i][j][k]!=1)
//								System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
//								
//						}
//						else
//							para_w[i][j][k]= -1.0;
//					}
//					else
//					{
//						if(k<para_noF)
//						{
//							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
//							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
//							{
//								para_w[i][j][k]= para_q[k]* var_mu[i];
//								if(para_w[i][j][k]!=0)
//									System.out.println("Val > 1: para["+i+"]["+j +"]["+k+"]="+para_w[i][j][k]);
//							}
//							else
//								para_w[i][j][k] = -1.0;
//						}
//						else
//							para_w[i][j][k] = -1.0;
//						
//					}
//				}
//			
//			xLst = shortestPath(g_prune, _d, para_w,funcNode);
//			if(xLst!=null && xLst.size()>0)
//			{
//				for (ArrayList<Integer> p : xLst)
//				{
//					//check if p is feasible
//					boolean isFeasible = CheckFeasible(p, _g, _d); 
//					if (isFeasible)
//					{
//						flag=2;
//						p_final = convertPath(p, _d, _g);
//						return p_final;
//					}
//				}
//			}					
//			//xet tung duong di
////			for (Double[][][] x_temp : xLst)
////			{
////				var_x = x_temp;
////				
////			}
//			
//			
//			
//		}
		flag =2;
		return null;
	
	}

	public static ArrayList<Integer> A_1(nDemand _d,nGraph _g)
	{

		fl=true;
		nGraph g_prune = prunedNetwork(_d, _g);
		int para_V = g_prune.getV();
		int para_noF= _d.getFunctions().size();
		double[][] var_gama = new double[para_V][para_V];
		double[] var_mu = new double[para_V];
		double[][] para_C = new double[para_V][para_V];
		double[] para_q = new double[para_noF];
		double[] para_bigP= new double[para_V];
		double[][][] para_w = new double[para_V][para_V][para_noF+1];
		double[][][] var_x = new double[para_V][para_V][para_noF+1];
		double para_b,para_p;
		ArrayList<Integer> p_final = new ArrayList<>();
		

		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				para_C[i][j]=g_prune.getEdgeWeight(i+1, j+1);
		for (int i=0;i< para_noF;i++)
			para_q[i] = getFunction(_d.getFunctions().get(i)).getLamda();
		
		for (int i=0;i<para_V;i++)
			para_bigP[i] = g_prune.getCap(i+1);
		para_b = _d.getBw();
		para_p = _d.getProcessReq();
		
		
		
		//khoi tao mot gia tri khong kha thi cua bien x
		
		
//		for (int i=0;i<para_V;i++)
//			for (int j=0;j<para_V;j++)
//				for (int k=0;k<para_noF+1;k++)
//					var_x[i][j][k]=0.0;
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				var_gama[i][j]=0.0;
		for (int i=0;i<para_V;i++)
			var_mu[i]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
					var_x[i][j][k]=0.0;
		
		for (int i=0;i<para_V;i++)
			for (int j=0;j<para_V;j++)
				for (int k=0;k<para_noF+1;k++)
				{
					if (i!=j )
					{
						if(para_C[i][j]>=para_b)
						{
							//para_w[i][j][k]= 1 + para_b* var_gama[i][j] + para_p* var_mu[j];
							para_w[i][j][k]= 1.0;
						}
						else
							para_w[i][j][k]= -1.0;
					}
					else
					{
						if(k<para_noF)
						{
							ArrayList<Integer> Z_i = getFunction(_d.getFunctions().get(k)).getVnfNode();
							//cap nho nhat la 0.15 
							
							if(Z_i.contains(i+1) && (_g.getCap(i+1)>=para_b+para_p))
								para_w[i][j][k]= 0.0;
							else
								para_w[i][j][k] = -1.0;
						}
						else
							para_w[i][j][k] = -1.0;
						
					}
				}		
		
			
			ArrayList<ArrayList<Integer>> xLst = shortestPath_new(g_prune, _d, para_w);
			if(xLst==null)
			{
				flag =1;
				return null;
				
			}
			else
			{
				for (ArrayList<Integer> p : xLst)
				{
					//check if p is feasible
					p_final = convertPath(p, _d, _g);
					
					boolean isFeasible = CheckFeasible(p_final, _g, _d); 
					
					if (isFeasible)
					{
						flag=0;
						//p_final = convertPath(p, _d, _g);
						return p_final;
					}
				}
			}
		flag =2;
		return null;
	
	}
	
	public static ArrayList<Integer> OptimalSimpleGraph(nDemand _d, nGraph _g)//theo new expanded graph (optimal 1)
	{

		//link_load, node load duoc cap nhat o day
		ArrayList<Integer> p = new ArrayList<>();
		nGraph g_used= new nGraph(_g.cap, _g.w);
		funLoc = new ArrayList<>();
		h = new ArrayList<>();
		boolean okFlag= false;
		ArrayList<Integer> minP = new ArrayList<>();
		ArrayList<Pair> minFunLoc= new ArrayList<>();
		int minLenth= Integer.MAX_VALUE;
		nGraph g_save = CreateExGraph(_g, _d);
		if(g_save==null)
		{
			fl=false;
			return null;
		}
		System.out.println("source: "+ source + ", destination: "+ destination);
		ArrayList<ArrayList<Integer>> pathLst = shortestPaths(source, destination, g_save, _d.getBw(),_d.getProcessReq());
		
		
		if(pathLst!=null && pathLst.size()>0)
		{
			for(int i=0;i<pathLst.size();i++)
			{

				funLoc = new ArrayList<>();
				okFlag=false;
				p=new ArrayList<>();
				g_used= new nGraph(_g.cap, _g.w);
				ArrayList<Integer> path = pathLst.get(i);			
				int start_org = 0;
				int end_org =0;
				int i1=0;
				for (int j=0;j<path.size()-1;j++)
				{
					int start = path.get(j);
					int end =	path.get(j+1);
					start_org = h.get(start-1);
					end_org = h.get(end-1);
					if(start_org!= end_org)
						p.add(start_org);
					else
					{
						funLoc.add(new Pair(start_org, _d.getFunctions().get(i1)));
						i1++;
					}
				}
				if(end_org!=0)
					p.add(end_org);
				//System.out.println(end_org+ "]");
				for (int j=0;j<p.size()-1;j++)
				{
					int start = p.get(j);
					int end = p.get(j+1);
					if(start != end)
					{
						double wei= g_used.getEdgeWeight(start, end);
						if(wei<_d.getBw())
						{
							okFlag=true;
							break;
						}
						else
						{
							g_used.setEdgeWeight(start, end, wei- _d.getBw());
						}
						
					}
					
						
				}
				for (int j=0;j<p.size();j++)
				{
					int start = p.get(j);
					double _cap = g_used.getCap(start);
					if(_cap<_d.getProcessReq())
					{
						okFlag = true;
						break;
					}
					else
						g_used.setCap(start, _cap-_d.getProcessReq());
				}
				if(okFlag)
					continue;
				else
				{
					if(p.size()<minLenth)
					{
						for (i1=0;i1<_d.getFunctions().size();i1++)
						{
							int idFun= _d.getFunctions().get(i1);
							
							for (int j=0;j<funLoc.size();j++)
							{
								Pair pr = funLoc.get(j);
								if(pr.getfunction() == idFun)
								{
									double mul = getFunction(idFun).getLamda();
									if(mul>g_used.getCap(pr.getnode()))
									{
										okFlag=true;
										break;
										
									}
									else
									{
										double c_temp= g_used.getCap(pr.getnode())-mul;
										g_used.setCap(pr.getnode(),c_temp );
									}
									
								}
							}
							if(okFlag)
								break;
						}
						if(!okFlag)
						{
							minLenth = p.size();
							minP= new ArrayList<>();
							minFunLoc = new ArrayList<>();
							for (i1 = 0;i1<p.size();i1++)
								minP.add(p.get(i1));
							for (i1=0;i1<funLoc.size();i1++)
								minFunLoc.add(funLoc.get(i1));
						}

						
					}
					
				}
				continue;				
			
			}
		}	
		else
		{
			flag = 1;
			fl=false;
			return null;
		}
		if(minP==null || minP.size()<=0)
		{
			flag=2;
			fl = false;
			return null;
		}
		else
			flag=0;
		
		fl=true;
		funLoc = new ArrayList<>();
		for (int i1=0;i1<minFunLoc.size();i1++)
			funLoc.add(minFunLoc.get(i1));
		return minP;		
	}
	public static int combinations(int noComb, ArrayList<Integer> arr, ArrayList<ArrayList<Integer>> list) {
		
		int numArrays = (int)Math.pow(arr.size(), noComb);
	    // Create each array
	    for(int i = 0; i < numArrays; i++) {
	        ArrayList<Integer> current = new ArrayList<>();
	        // Calculate the correct item for each position in the array
	        for(int j = 0; j < noComb; j++) {
	            // This is the period with which this position changes, i.e.
	            // a period of 5 means the value changes every 5th array
	            int period = (int) Math.pow(arr.size(), noComb - j - 1);
	            // Get the correct item and set it
	            int index = i / period % arr.size();
	            current.add(arr.get(index));
	        }
	        list.add(current);
	    	}
	    return list.size();
	    }
	public static ArrayList<Integer> optimal(nDemand _d, nGraph _g)//theo new expanded graph (optimal 2)
	{

		//link_load, node load duoc cap nhat o day
		ArrayList<Integer> p = new ArrayList<>();
		nGraph g_used= new nGraph(_g.cap, _g.w);
		funLoc = new ArrayList<>();
		h = new ArrayList<>();
		boolean okFlag= false;
		ArrayList<Integer> minP = new ArrayList<>();
		ArrayList<Pair> minFunLoc= new ArrayList<>();
		int minLenth= Integer.MAX_VALUE;
		nGraph g_save = CreateExGraph(_g, _d);
		if(g_save==null)
		{
			fl=false;
			return null;
		}
		System.out.println("source: "+ source + ", destination: "+ destination);
		ArrayList<ArrayList<Integer>> pathLst = shortestPaths(source, destination, g_save, _d.getBw(),_d.getProcessReq());
		
		
		if(pathLst!=null && pathLst.size()>0)
		{
			for(int i=0;i<pathLst.size();i++)
			{

				funLoc = new ArrayList<>();
				okFlag=false;
				p=new ArrayList<>();
				g_used= new nGraph(_g.cap, _g.w);
				ArrayList<Integer> path = pathLst.get(i);			
				int start_org = 0;
				int end_org =0;
				int i1=0;
				for (int j=0;j<path.size()-1;j++)
				{
					int start = path.get(j);
					int end =	path.get(j+1);
					start_org = h.get(start-1);
					end_org = h.get(end-1);
					if(start_org!= end_org)
						p.add(start_org);
					else
					{
						funLoc.add(new Pair(start_org, _d.getFunctions().get(i1)));
						i1++;
					}
				}
				if(end_org!=0)
					p.add(end_org);
				for (int j=0;j<p.size()-1;j++)
				{
					int start = p.get(j);
					int end = p.get(j+1);
					if(start != end)
					{
						double wei= g_used.getEdgeWeight(start, end);
						if(wei<_d.getBw())
						{
							okFlag=true;
							break;
						}
						else
						{
							g_used.setEdgeWeight(start, end, wei- _d.getBw());
						}						
					}				
						
				}
				for (int j=0;j<p.size();j++)
				{
					int start = p.get(j);
					double _cap = g_used.getCap(start);
					if(_cap<_d.getProcessReq())
					{
						okFlag = true;
						break;
					}
					else
						g_used.setCap(start, _cap-_d.getProcessReq());
				}
				if(okFlag)
					continue;
				else
				{
					if(p.size()<minLenth)
					{
						for (i1=0;i1<_d.getFunctions().size();i1++)
						{
							int idFun= _d.getFunctions().get(i1);
							
							for (int j=0;j<funLoc.size();j++)
							{
								Pair pr = funLoc.get(j);
								if(pr.getfunction() == idFun)
								{
									double mul = getFunction(idFun).getLamda();
									if(mul>g_used.getCap(pr.getnode()))
									{
										okFlag=true;
										break;
										
									}
									else
									{
										double c_temp= g_used.getCap(pr.getnode())-mul;
										g_used.setCap(pr.getnode(),c_temp );
									}
									
								}
							}
							if(okFlag)
								break;
						}
						if(!okFlag)
						{
							minLenth = p.size();
							minP= new ArrayList<>();
							minFunLoc = new ArrayList<>();
							for (i1 = 0;i1<p.size();i1++)
								minP.add(p.get(i1));
							for (i1=0;i1<funLoc.size();i1++)
								minFunLoc.add(funLoc.get(i1));
						}

						
					}
					
				}			
			
			}
		}	
		else
		{
			fl=false;
			return null;
		}
		if(minP==null || minP.size()<=0)
		{
			System.out.println("Blocking of type 2");
			//thuc hien buoc 5
			//tim tat ca nhung link bi vuot 
			
			//Chon 1 duong ngau nhien, kiem tra xem co du tai nguyen ko
			int dem= 0;
			minP = new ArrayList<>();
			minFunLoc= new ArrayList<>();
			minLenth= Integer.MAX_VALUE;
			for (int pId = 0;pId < pathLst.size();pId++)
			{
				
				okFlag=true;
				funLoc = new ArrayList<>();
				p=new ArrayList<>();
				ArrayList<Integer> path = pathLst.get(pId);			
				int start_org = 0;
				int end_org =0;
				//System.out.print("real 4:[");
				int i1=0;
				for (int j=0;j<path.size()-1;j++)
				{
					int start = path.get(j);
					int end =	path.get(j+1);
					start_org = h.get(start-1);
					end_org = h.get(end-1);
					if(start_org!= end_org)
						p.add(start_org);
					else
					{
						funLoc.add(new Pair(start_org, _d.getFunctions().get(i1)));
						i1++;
					}
				}
				if(end_org!=0)
					p.add(end_org);
				//System.out.println(end_org+ "]");
				ArrayList<wLink> linkLst = new ArrayList<>();
				boolean existLink = false;
				
				ArrayList<Integer> oldLst = new ArrayList<>();
				for (int j=0;j<=_d.getFunctions().size();j++)
				{
					oldLst.add(j+1);
				}
				
				for (int j=0;j<p.size()-1;j++)
				{
					int start = p.get(j);
					int end = p.get(j+1);
					if(start != end)
					{
						existLink = false;
						wLink l1 = new wLink(start,end,1,oldLst);
						for (int j1=0;j1<linkLst.size();j1++) {
							if (linkLst.get(j1).CompareTo(l1))
							{
								existLink = true;
								l1.setWeight(linkLst.get(j1).getWeight()+1);
								linkLst.set(j1, l1);
								break;
							}
						}
						if(!existLink)
							linkLst.add(l1);
					}
				}	
				
				// ktra xem link nao bi vi pham
				ArrayList<wLink> violatedLink = new ArrayList<>();
				for (wLink l:linkLst)
				{
					if(_g.getEdgeWeight(l.getStart(), l.getEnd())<l.getWeight()*_d.getBw())
					{
						Double t = _g.getEdgeWeight(l.getStart(), l.getEnd())/_d.getBw();
						l.setWeight(t);
						violatedLink.add(l);
					}
				}
					
				
				// Xet 2 loai node vi pham
				//Node loai 1: Loai vi pham vi cung cap function
				
				ArrayList<Node> nodeLst= new ArrayList<>();
				boolean existNode = false;
				//Dang xet la function require nhu nhau.				
				//ktra xem node nao bi vi pham
				oldLst = new ArrayList<>();
				for (int j=1;j<=_d.getFunctions().size();j++)
				{
					oldLst.add(j);
				}
				
				for (int j=0;j<funLoc.size();j++)
				{
					Pair pr = funLoc.get(j);
					double mul = getFunction(pr.getfunction()).getLamda()+_d.getProcessReq();
					Node _node = new Node(pr.getnode(), mul,1,oldLst);
					existNode= false;
					for (int i=0;i<nodeLst.size();i++)
					{
						if(nodeLst.get(i).CompareTo(_node))
						{
							existNode = true;
							double c_temp = nodeLst.get(i).getReq()+mul;
							nodeLst.get(i).setReq(c_temp);
							nodeLst.get(i).setusedNo(nodeLst.get(i).getusedNo()+1);
							break;
						}
					}
					if(!existNode)
						nodeLst.add(_node);
				}
				
				ArrayList<Node> violatedNode1 = new ArrayList<>();
				for (Node node:nodeLst)
				{
					if(node.getReq()> _g.getCap(node.getid()))
					{
						double capacity = _g.getCap(node.getid());
						double requirement = getFunction(_d.getFunctions().get(0)).getLamda()+_d.getProcessReq();
						int t= (int)(capacity/requirement) ;
						node.setusedNo(t);
						violatedNode1.add(node);
					}
				}
				
				
				
				ArrayList<Node> nodeLst1= new ArrayList<>();
				existNode = false;
				//Dang xet la function require nhu nhau.				
				//ktra xem node nao bi vi pham
				oldLst = new ArrayList<>();
				for (int j=1;j<=_d.getFunctions().size()+1;j++)
				{
					oldLst.add(j);
				}
				
				
				//Truong hop node vi pham loai 2: khong chua function
				for (int j=0;j<p.size();j++)
				{
					int start = p.get(j);
					double mul = _d.getProcessReq();
					Node _node = new Node(start, mul,1,oldLst);
					boolean type1=false;
					for (int i=0;i<nodeLst.size();i++)
					{
						if(nodeLst.get(i).CompareTo(_node))
						{
							type1=true;
							break;
						}
					}
					if(!type1)
					{
						existNode= false;
						for (int i=0;i<nodeLst1.size();i++)
						{
							if(nodeLst1.get(i).CompareTo(_node))
							{
								existNode = true;
								double c_temp = nodeLst1.get(i).getReq()+mul;
								nodeLst1.get(i).setReq(c_temp);
								break;
							}
						}
						if(!existNode)
							nodeLst1.add(_node);
					}				
				
				}					
				
				ArrayList<Node> violatedNode2 = new ArrayList<>();
				for (Node node:nodeLst1)
				{
					if(node.getReq()> _g.getCap(node.getid()))
					{
						double capacity = _g.getCap(node.getid());
						double requirement = _d.getProcessReq();
						
						//so luong khong duoc su dung trong 6 set
						
						int t= _d.getFunctions().size()+1-(int)(capacity/requirement) ;
						node.setusedNo(t);
						violatedNode2.add(node);
					}
				}
								
				if(violatedLink.size()==0&& violatedNode1.size()==0 && violatedNode2.size()==0)
				{
					fl=false;
					return null;
				}
				
				int combSum1=1;
				int combSum2=1;
				int combSum3=1;

				int limitLoop =10;
				for (wLink l:violatedLink)
				{
					int length = (int) l.getWeight();
					ArrayList<ArrayList<Integer>> listComb = new ArrayList<>();
					int numberofComb = combinations(length, l.getCnnSet(), listComb);
					l.setCnnSetComb(listComb);	
					combSum1=combSum1*numberofComb;
				}
				for (Node node:violatedNode1)
				{
					//int length = (int) l.getWeight();
					ArrayList<ArrayList<Integer>> listComb = new ArrayList<>();
					int numberofComb = combinations(node.getusedNo(), node.getvSetLst(), listComb);
					node.setvSetComb(listComb);	
					combSum2=combSum2*numberofComb;
				}
				for (Node node:violatedNode2)
				{
					//int length = (int) l.getWeight();
					ArrayList<ArrayList<Integer>> listComb = new ArrayList<>();
					int numberofComb = combinations(node.getusedNo(), node.getvSetLst(), listComb);
					node.setvSetComb(listComb);	
					combSum3=combSum3*numberofComb;
				}
				
				
				//quyet dinh remove nhung link ay trong tap cnnset nao
				ArrayList<Integer> demArr = new ArrayList<>();
				for (int i=0;i<violatedLink.size();i++)
					demArr.add(0);
				
				while (dem<limitLoop)
				{
					ArrayList<wLink> updateLink = new ArrayList<>();
					System.out.println("Thu lan::: "+ dem);
					dem++;
					if(violatedLink.size()>0)
					{
						for (int i= 0;i<violatedLink.size();i++)
						{
							//xet tung link
							wLink linkTemp = violatedLink.get(i);
							ArrayList<ArrayList<Integer>> listComb = linkTemp.getCnnSetComb();
							int rand = UtilizeFunction.randInt(0, listComb.size()-1);
							linkTemp.setCnnSet(listComb.get(rand));
							updateLink.add(linkTemp);
						}
					}
					ArrayList<Node> updateNode1 = new ArrayList<>();
					if(violatedNode1.size()>0)
					{
						for(int i=0;i<violatedNode1.size();i++)
						{
							
							//update lai so node co the su dung cho node do bang cach chia cap cho max function
							Node _node = violatedNode1.get(i);
							ArrayList<ArrayList<Integer>> listComb = _node.getvSetComb();
							int rand = UtilizeFunction.randInt(0, listComb.size()-1);
							_node.setvSetLst(listComb.get(rand));
							updateNode1.add(_node);
						}
					}
					ArrayList<Node> updateNode2 = new ArrayList<>();
					if(violatedNode2.size()>0)
					{
						for(int i=0;i<violatedNode2.size();i++)
						{
							
							//update lai so node co the su dung cho node do bang cach chia cap cho max function
							Node _node = violatedNode2.get(i);
							ArrayList<ArrayList<Integer>> listComb = _node.getvSetComb();
							int rand = UtilizeFunction.randInt(0, listComb.size()-1);
							_node.setvSetLst(listComb.get(rand));
							updateNode2.add(_node);
						}
					}
					
					
					p = new ArrayList<>();
					g_used= new nGraph(_g.cap, _g.w);
					funLoc = new ArrayList<>();
					h = new ArrayList<>();
					okFlag= false;
					
					g_save = CreateExGraph(_g, _d, updateLink,updateNode1,updateNode2);
					if(g_save==null)
					{
						fl=false;
						return null;
					}
					System.out.println("source: "+ source + ", destination: "+ destination);
					ArrayList<ArrayList<Integer>> pathLstNew = shortestPaths(source, destination, g_save, _d.getBw(),_d.getProcessReq());
					if(pathLstNew!=null && pathLstNew.size()>0)
					{
//
//						for(int i=0;i<pathLstNew.size();i++)
//						{
//							System.out.print(i+":[");
//							for (int j=0;j<pathLstNew.get(i).size();j++)
//								System.out.print( pathLstNew.get(i).get(j)+" ");
//							System.out.println("]");
//						}
						for(int i=0;i<pathLstNew.size();i++)
						{

							funLoc = new ArrayList<>();
							okFlag=false;
							p=new ArrayList<>();
							//Chon 1 duong ngau nhien, kiem tra xem co du tai nguyen ko
							g_used= new nGraph(_g.cap, _g.w);
							path = pathLstNew.get(i);			
							start_org = 0;
							end_org =0;
							i1=0;
							for (int j=0;j<path.size()-1;j++)
							{
								int start = path.get(j);
								int end =	path.get(j+1);
								start_org = h.get(start-1);
								end_org = h.get(end-1);
								if(start_org!= end_org)
									p.add(start_org);
								else
								{
									funLoc.add(new Pair(start_org, _d.getFunctions().get(i1)));
									i1++;
								}
								//System.out.print(start_org+ " ");
							}
							if(end_org!=0)
								p.add(end_org);
							//System.out.println(end_org+ "]");
							for (int j=0;j<p.size()-1;j++)
							{
								int start = p.get(j);
								int end = p.get(j+1);
								if(start!=end)
								{
									double wei= g_used.getEdgeWeight(start, end);
									if(wei<_d.getBw())
									{
										okFlag=true;
										break;
									}
									else
									{
										g_used.setEdgeWeight(start, end, wei- _d.getBw());
									}
								}
								
									
							}
							for (int j=0;j<p.size();j++)
							{
								int start = p.get(j);
								double _cap = g_used.getCap(start);
								if(_cap<_d.getProcessReq())
								{
									okFlag = true;
									break;
								}
								else
									g_used.setCap(start, _cap-_d.getProcessReq());
							}
							if(okFlag)
								continue;
							okFlag=false;
							for (i1=0;i1<_d.getFunctions().size();i1++)
							{
								int idFun= _d.getFunctions().get(i1);
								
								for (int j=0;j<funLoc.size();j++)
								{
									Pair pr = funLoc.get(j);
									if(pr.getfunction() == idFun)
									{
										double mul = getFunction(idFun).getLamda();
										if(mul>g_used.getCap(pr.getnode()))
										{
											okFlag=true;
											break;											
										}
										else
										{
											double c_temp= g_used.getCap(pr.getnode())-mul;
											g_used.setCap(pr.getnode(),c_temp );
										}
										
									}
								}
								if(okFlag)
									break;
							}

							
							if(!okFlag)
							{
								if(p.size()<minLenth)
								{
									minLenth = p.size();
									minP= new ArrayList<>();
									minFunLoc = new ArrayList<>();
									for (i1 = 0;i1<p.size();i1++)
										minP.add(p.get(i1));
									for (i1=0;i1<funLoc.size();i1++)
										minFunLoc.add(funLoc.get(i1));
								}
							}
						
						}				
					}
							
				}
				if(minP!=null && minP.size()>0)
				{
					System.out.println("aaaaa: "+ minP.size());
					break;
				}
			}
			
		}
		
		if(minP==null || minP.size()<=0)
		{
			fl = false;
			return null;
		}
		
		fl=true;
		funLoc = new ArrayList<>();
		for (int i1=0;i1<minFunLoc.size();i1++)
			funLoc.add(minFunLoc.get(i1));
		return minP;	
	
	
	
	
	
	}	
	private static VertexFactory<Object> vertexFactory = new VertexFactory<Object>()
    {
        private int i;

        @Override
        public Object createVertex()
        {
            return ++i;
        }
    };
//    private static VertexFactory<Integer> vertexFactoryInteger = new VertexFactory<Integer>()
//    	    {
//    	        private int i=0;
//
//    	        @Override
//    	        public Integer createVertex()
//    	        {
//    	            return ++i;
//    	        }
//    	    };
    public static void CreateGraph(int NoVertex,double p,double _cap, double _w)
    {

     
  	final int seed = 1;
      final double edgeProbability = p;
      final int numberVertices = NoVertex;

      GraphGenerator<Integer, DefaultWeightedEdge, Integer> gg =
              new GnpRandomGraphGenerator<Integer, DefaultWeightedEdge>(
                  numberVertices, edgeProbability, seed, false);
      DefaultDirectedGraph<Integer, DefaultWeightedEdge> graph =
              new DefaultDirectedGraph<>(DefaultWeightedEdge.class);
      VertexFactory<Integer> vertexFactoryInteger= new VertexFactory<Integer>() {
      	 private int i=0;

	        @Override
	        public Integer createVertex()
	        {
	            return ++i;
	        }
		};
          gg.generateGraph(graph, vertexFactoryInteger, null);
  	
      //set cap and bandwidth cho do thi g
      g = new nGraph(NoVertex);
      int noE = 0;
      for (DefaultWeightedEdge edges : graph.edgeSet()) {
      	
      	int s = Integer.parseInt(graph.getEdgeSource(edges).toString());
      	int t = Integer.parseInt(graph.getEdgeTarget(edges).toString());
			//System.out.println("Dinh: "+ s+ "..." + t+ "..."+w);
			//double w= UtilizeFunction.randomDouble(new Integer[] {5000,6000,7000,8000,9000,10000});
			if(s!=t)
			{
				g.setEdgeWeight(s, t, _w);
				noE++;
			}
			else
				System.out.println("Loop");
		}
	   	for (int i=0;i<g.getV();i++)
     {
	   		//int index = UtilizeFunction.randInt(0, dataReal.size()-1);
	      	  //Vector<Double> data = dataReal.get(index);
	      	  
	      	  g.setCap(i+1, _cap);
     }    
	   	noVertex = g.getV();
	   	E = noE;
      
      
  
    }
    
    public static void CreateGraphFromFile(String fileName,double cap_max,double cap_min, double w_max,double w_min)
    {
    	
    	int numberVertex= 0;
		E =0;
		File file = new File(fileName);
        try {
			in = new BufferedReader(new FileReader(file));
			//First line -> set of parameters
//			String[] tempLine=in.readLine().split(" ");
//			noVertex= Integer.parseInt(tempLine[0]);
//			E = Integer.parseInt(tempLine[1]);
//			noFunction= Integer.parseInt(tempLine[2]);
//			prob = Double.parseDouble(tempLine[3]);
//			tempLine = in.readLine().split(";"); 
			 DefaultDirectedGraph<String, DefaultWeightedEdge> graph =
		                new DefaultDirectedGraph<>(DefaultWeightedEdge.class);
			
			//so node;
			boolean _finished= false;
			while(true)
			{
				String ln= in.readLine();
				if(ln!=null)
				{

					String[] line= ln.split(" ");
					if(line[0].equals("NODES"))
					{
						while(true)
						{
							String node_line = in.readLine();
							if(node_line.equals(")"))
								break;
							else
							{
								//node_line.replaceAll("^\\s*", "");
								String[] nodeStr = node_line.split(" ");
								graph.addVertex(nodeStr[2]);
								numberVertex++;
								
							}
						}
						
					}
					else
					{
						if(line[0].equals("LINKS"))
						{
							
							while(true)
							{
								String link_line= in.readLine();
								if(link_line.equals(")"))
								{
									_finished=true;
									break;
								}
								else
								{
									//link_line.replaceFirst("^\\s*", "");
									String[] linkStr = link_line.split(" ");
									String[] edgeStr = linkStr[2].split("_");
									graph.addEdge(edgeStr[0], edgeStr[1]);
								}
							}
							if(_finished)
								break;
						}
						else
							continue;
					}
				}
			}
			noVertex= numberVertex;
			Vector<Double> cap = new Vector<Double>(numberVertex);
			ArrayList<List<Double>> w = new ArrayList<List<Double>>();			
			
			for (int i=0;i<noVertex;i++)
			{
				ArrayList<Double> temp= new ArrayList<>();
				for(int j=0;j<noVertex;j++)
				{
					temp.add(0.0);
				}
				w.add(temp);
			}
			ArrayList<String> verLst = new ArrayList<>();
			for(String node:graph.vertexSet())
			{
				verLst.add(node);
				if(node.matches(".*\\d.*"))
					cap.add(cap_min);
				else
					cap.add(cap_max);
			}
			for(DefaultWeightedEdge e:graph.edgeSet())
			{
				E++;
				String src= graph.getEdgeSource(e);
				String dest = graph.getEdgeTarget(e);
				int idSrc = verLst.indexOf(src);
				int idDest = verLst.indexOf(dest);
				if(!src.matches(".*\\d.*") && !dest.matches(".*\\d.*"))
				{
					w.get(idSrc).set(idDest, w_max);
				}
				else
					w.get(idSrc).set(idDest, w_min);
				
				
			}
			g= new nGraph(cap,w);
            // Always close files.
            in.close();  
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	
	
    }
    
    public static void CreateRandomGraph(int NoVertex,int NoEdge,double p,int _capacity)
    {
//        DirectedGraph<Object, DefaultEdge> graph = new DefaultDirectedGraph<>(DefaultEdge.class);
//        ScaleFreeGraphGenerator<Object, DefaultEdge> generator = new ScaleFreeGraphGenerator<>(NoVertex);
//        generator.generateGraph(graph, vertexFactory, null);
 

         
    	//UndirectedGraph<Object, DefaultEdge> graph = new SimpleGraph<>(DefaultEdge.class);
    	//RandomGraphGenerator<Object, DefaultEdge> generator= new RandomGraphGenerator<>(NoVertex, NoEdge);
    	//generator.generateGraph(graph, vertexFactory, null);
       
    	final int seed = 1;
        final double edgeProbability = p;
        final int numberVertices = NoVertex;

        GraphGenerator<Integer, DefaultWeightedEdge, Integer> gg =
                new GnpRandomGraphGenerator<Integer, DefaultWeightedEdge>(
                    numberVertices, edgeProbability, seed, false);
//        GraphGenerator<Integer, DefaultWeightedEdge, Integer> gg =
//            new GnpRandomGraphGenerator<Integer, DefaultWeightedEdge>(
//                numberVertices, edgeProbability, seed, false);
//        
//        WeightedPseudograph<Integer, DefaultWeightedEdge> graph =
//                new WeightedPseudograph<>(DefaultWeightedEdge.class);
        
        DefaultDirectedGraph<Integer, DefaultWeightedEdge> graph =
                new DefaultDirectedGraph<>(DefaultWeightedEdge.class);
        VertexFactory<Integer> vertexFactoryInteger= new VertexFactory<Integer>() {
        	 private int i=0;

 	        @Override
 	        public Integer createVertex()
 	        {
 	            return ++i;
 	        }
		};
            gg.generateGraph(graph, vertexFactoryInteger, null);
    	
        //set cap and bandwidth cho do thi g
        g = new nGraph(NoVertex);
        int noE = 0;
        for (DefaultWeightedEdge edges : graph.edgeSet()) {
        	
        	int s = Integer.parseInt(graph.getEdgeSource(edges).toString());
        	int t = Integer.parseInt(graph.getEdgeTarget(edges).toString());
			//System.out.println("Dinh: "+ s+ "..." + t+ "..."+w);
			//double w= UtilizeFunction.randomDouble(new Integer[] {5000,6000,7000,8000,9000,10000});
			if(s!=t)
			{
				g.setEdgeWeight(s, t, 1);
				noE++;
			}
			else
				System.out.println("Loop");
		}
	   	for (int i=0;i<g.getV();i++)
       {
	   		//int index = UtilizeFunction.randInt(0, dataReal.size()-1);
	      	  //Vector<Double> data = dataReal.get(index);
	      	  
	      	  g.setCap(i+1, _capacity);
       }    
	   	noVertex = g.getV();
	   	E = noE;
        
        
    }
    public static void CreateInput(int NoVertex,int NoFunc,double p, String fileName,int NoNode,double _cap, double _w, double _q)
    {


		DecimalFormat df = new DecimalFormat("#.####");
		BufferedWriter out;
        try {        	
	    	out= new BufferedWriter(new FileWriter(fileName));
	    	CreateGraph(NoVertex,p,_cap,_w);
			functionArr = new ArrayList<>();
		    for (int i=0;i< 10;i++)
		       functionArr.add(new nFunction(_q,i+1,g.getV(),NoNode));
		    //ghi ra file
		    out.write(NoVertex+" "+ E+" "+NoFunc +" "+p );
		    out.newLine();
		    for (int i=0;i<NoFunc;i++)
		    {
	               out.write(df.format(functionArr.get(i).getLamda())+";");
	               for (Integer _i : functionArr.get(i).getVnfNode()) {
	            	   
					out.write(_i+" ");
				}
	               out.newLine();
	               
	       	}
	       	for (int i=0;i<NoVertex;i++)
	       	{		            
	       		out.write(df.format(g.getCap(i+1)));	            
	       		out.newLine();
	       	}
	       	for (int i=0;i<NoVertex;i++)
	       	{
	       		for (int j=0;j<NoVertex;j++)
	       			out.write(df.format(g.getEdgeWeight(i+1, j+1)) + " ");
	       		out.newLine();
	       	}
	       	out.close();
			} catch (IOException e) {
			e.printStackTrace();
		}   	
    
	
    }
	
    public static void WriteDataFromFile(int NoFunc,String fileName,int NoNode,String fileInput,double p_max,double p_min,double w_max,double w_min)
    {


		DecimalFormat df = new DecimalFormat("#.####");
		BufferedWriter out;
        try {        	
	    	out= new BufferedWriter(new FileWriter(fileName));
	    	CreateGraphFromFile(fileInput,p_max,p_min,w_max,w_min);
	    	//CreateRandomGraph(NoVertex,NoEdge,p,_capacity);
			functionArr = new ArrayList<>();
		    for (int i=0;i< 10;i++)
		       functionArr.add(new nFunction(0.1,i+1,g.getV(),NoNode));
		    //ghi ra file
		    double p=0.01;
		    out.write(g.getV()+" "+ E+" "+NoFunc+" "+p );
		    out.newLine();
		    for (int i=0;i<NoFunc;i++)
		    {
	               out.write(df.format(functionArr.get(i).getLamda())+";");
	               for (Integer _i : functionArr.get(i).getVnfNode()) {
	            	   
					out.write(_i+" ");
				}
	               out.newLine();
	               
	       	}
	       	for (int i=0;i<g.getV();i++)
	       	{		            
	       		out.write(df.format(g.getCap(i+1)));	            
	       		out.newLine();
	       	}
	       	for (int i=0;i<g.getV();i++)
	       	{
	       		for (int j=0;j<g.getV();j++)
	       			out.write(df.format(g.getEdgeWeight(i+1, j+1)) + " ");
	       		out.newLine();
	       	}
	       	out.close();
			} catch (IOException e) {
			e.printStackTrace();
		}   	
    
	
    }
    public static void WriteSmallData(int NoVertex,int NoFunc,double p, String fileName,int NoNode,int _nodeCap, int _linkCap,double _q)
    {
    	default_p = 0.5;
    	default_b = 1.0;
		DecimalFormat df = new DecimalFormat("#.####");
		BufferedWriter out;
        try {  
        	out= new BufferedWriter(new FileWriter(fileName));
        	CreateGraph(NoVertex,p,_nodeCap,_linkCap);
			functionArr = new ArrayList<>();
		    for (int i=0;i< 10;i++)
		       functionArr.add(new nFunction(_q,i+1,g.getV(),NoNode));
		    //ghi ra file
		    
		    out.write ("#\r\n");
		    out.write ("# Test data\r\n");
		    out.write ("#\r\n");
		    out.write("param p_no_nodes :=" + noVertex +";\r\n");
		    out.write("set p_links := \r\n");
		    for (int i=0;i<NoVertex;i++)
		    {
		    	for(int j=0;j<NoVertex;j++)
		    	{
		    		if(i!=j && g.getEdgeWeight(i+1, j+1)>0)
		    			out.write((i+1) + " "+ (j+1)+ "\r\n");
		    	}
		    }
		    out.write(";\r\n");
		    out.write("param C :=\r\n");
		    for (int i=0;i<NoVertex;i++)
		    {
		    	for(int j=0;j<NoVertex;j++)
		    	{
		    		if(i!=j && g.getEdgeWeight(i+1, j+1)>0)
		    			out.write((i+1) + " "+ (j+1) +" "+ _linkCap+ "\r\n");
		    	}
		    }
		    out.write(";\r\n");
		    int ori = UtilizeFunction.randInt(1, noVertex);
		    int dest = UtilizeFunction.randInt(1, noVertex);
		    while (ori==dest)
		    {
		    	dest= UtilizeFunction.randInt(1, noVertex);
		    }
		    out.write("param origin := " + ori+ ";\r\n");
		    out.write("param dest :=" + dest + ";\r\n");
		    
		    out.write("#\r\n");
		    out.write("# These 2 parameters are the values of b and p of the paper\r\n");
		    out.write("param default_p :="+ default_p + ";\r\n");
		    out.write("param default_b :="+ default_b + ";\r\n");
		    out.write("#\r\n");
		    out.write("#\r\n");
		    
		    out.write("param no_functions := "+ NoFunc + ";\r\n");
		    out.write("param q := \r\n");
		    for (int i=0;i<NoFunc;i++)
		    {
	               out.write(i+1 + " "+ df.format(functionArr.get(i).getLamda())+"\r\n");
		    }
		    out.write(";\r\n");
		    
		    out.write("param P := \r\n");
		    for (int i=0;i<NoVertex;i++)
		    {
	               out.write(i+1 + " "+ df.format(g.getCap(i+1))+"\r\n");
		    }
		    out.write(";\r\n");
		    
		    out.write("#\r\n");
		    out.write("#  This is the incidence matrix for functions and nodes \r\n");
		    out.write("#  f_nodes[i,k] = 1 if node i contains function k \r\n");
		    out.write ("#  Only the elements with value 1 need be given.\r\n");
		    out.write("#\r\n");
		    
		    out.write("param: f_nodes :=\r\n");
		    for(int i=0;i<NoVertex;i++)
		    {
		    	for(int j=0;j<NoFunc;j++)
		    	{
		    		for (Integer _i : functionArr.get(j).getVnfNode()) {
		            	if(_i == i+1)   
		            		out.write(_i+" "+(j+1)+" 1\r\n" );
					}
		    	}
		    }
		    out.write(";");
		    out.close();
			} catch (IOException e) {
			e.printStackTrace();
		}   	
    
	
    }
    
	public static void WriteData(int NoVertex,int NoEdge,int NoFunc,double p, String fileName,int NoNode,int _capacity)
	{

		DecimalFormat df = new DecimalFormat("#.####");
		BufferedWriter out;
        try {        	
	    	out= new BufferedWriter(new FileWriter(fileName));
	    	CreateRandomGraph(NoVertex,NoEdge,p,_capacity);
			functionArr = new ArrayList<>();
		    for (int i=0;i< 10;i++)
		       functionArr.add(new nFunction(0.1,i+1,g.getV(),NoNode));
		    //ghi ra file
		    out.write(NoVertex+" "+ E+" "+NoFunc +" "+p );
		    out.newLine();
		    for (int i=0;i<NoFunc;i++)
		    {
	               out.write(df.format(functionArr.get(i).getLamda())+";");
	               for (Integer _i : functionArr.get(i).getVnfNode()) {
	            	   
					out.write(_i+" ");
				}
	               out.newLine();
	               
	       	}
	       	for (int i=0;i<NoVertex;i++)
	       	{		            
	       		out.write(df.format(g.getCap(i+1)));	            
	       		out.newLine();
	       	}
	       	for (int i=0;i<NoVertex;i++)
	       	{
	       		for (int j=0;j<NoVertex;j++)
	       			out.write(df.format(g.getEdgeWeight(i+1, j+1)) + " ");
	       		out.newLine();
	       	}
	       	out.close();
			} catch (IOException e) {
			e.printStackTrace();
		}   	
    
	}
	public static int computeDiameter(String fileName)
	{
		
		File file = new File(fileName);
		functionArr = new ArrayList<nFunction>();
		DemandArray = new ArrayList<nDemand>();
		ArrayList<Integer> vnfNodeLst = new ArrayList<Integer>();
        try {
			in = new BufferedReader(new FileReader(file));
			//First line -> set of parameters
			String[] tempLine=in.readLine().split(" ");
			noVertex= Integer.parseInt(tempLine[0]);
			E = Integer.parseInt(tempLine[1]);
			noFunction= Integer.parseInt(tempLine[2]);
			prob = Double.parseDouble(tempLine[3]);
			//second line -> set of Functions
			for (int i=0;i<noFunction;i++)
			{
				vnfNodeLst = new ArrayList<Integer>();
				tempLine = in.readLine().split(";"); 
				double lamda= Double.parseDouble(tempLine[0]);
				String[] nodeLine = tempLine[1].split(" ");
				for(int j=0; j< nodeLine.length;j++)
					vnfNodeLst.add(Integer.parseInt(nodeLine[j]));
				functionArr.add(new nFunction(i+1,lamda,vnfNodeLst));
			}
			//luu vao mang noVertex+1 chieu
			
			Vector<Double> cap = new Vector<Double>(noVertex+1);
			ArrayList<List<Double>> w = new ArrayList<List<Double>>();			
			
			for (int i=0;i <noVertex;i++)
			{
				double _cap = Double.parseDouble(in.readLine());
	   	        cap.add(_cap);
			}
			
			for (int i=0;i<noVertex;i++)
			{
				ArrayList<Double> temp= new ArrayList<>();
				tempLine = in.readLine().split(" ");
				for(int j=0;j<noVertex;j++)
				{
					temp.add(Double.parseDouble(tempLine[j]));
				}
				w.add(temp);
			}
			g= new nGraph(cap,w);
            // Always close files.
            in.close();  
		} catch (IOException e) {
			e.printStackTrace();
		}
        
        int max=0;
        int len =0;
        for(int i=0;i<g.getV();i++)
        	for (int j=0;j<g.getV();j++)
        	{
        		if(i!=j)
        		{
        		ArrayList<ArrayList<Integer>> plst = SP(i+1,j+1,g);
        		if (plst!=null)
        		{
        			for(int k=0;k<plst.size();k++)
        			{
        				len = plst.get(k).size();
        				if(len>max)
        					max=len;
        			}
        		}	
        		}
        	}
		
	return max;
	
	}
	public static void ReadSmallData(String fileName)
	{
		
		File file = new File(fileName);
		functionArr = new ArrayList<nFunction>();
		DemandArray = new ArrayList<nDemand>();
		ArrayList<Integer> vnfNodeLst = new ArrayList<Integer>();
        try {
			in = new BufferedReader(new FileReader(file));
			// 3 first lines
			in.readLine();
			in.readLine();
			in.readLine();
			noVertex = Integer.parseInt(in.readLine().replaceAll("\\D+",""));
			
			//Set of links
			
			Vector<Double> cap = new Vector<Double>(noVertex+1);
			ArrayList<List<Double>> w = new ArrayList<List<Double>>();			
			
			for (int i=0;i <noVertex;i++)
			{
				double _cap = 0.0;
	   	        cap.add(_cap);
			}
			
			for (int i=0;i<noVertex;i++)
			{
				ArrayList<Double> temp= new ArrayList<>();
				for(int j=0;j<noVertex;j++)
				{
					temp.add(0.0);
				}
				w.add(temp);
			}
			//read links
			String st_temp = in.readLine();
			while (!st_temp.equals(";"))
			{
				st_temp = in.readLine();
			}
			in.readLine();
			//read cap for links
			st_temp = in.readLine();
			while (!st_temp.equals(";"))
			{
				int _s = Integer.parseInt(st_temp.split(" ")[0]);
				int _t = Integer.parseInt(st_temp.split(" ")[1]);
				double _w = Double.parseDouble(st_temp.split(" ")[2]);
				w.get(_s-1).set(_t-1, _w);
				st_temp = in.readLine();
			}
			
			source = Integer.parseInt(in.readLine().replaceAll("\\D+",""));
			destination = Integer.parseInt(in.readLine().replaceAll("\\D+",""));
			
			//2 comment lines
			in.readLine();
			in.readLine();
			default_p = Double.parseDouble(in.readLine().replaceAll("\\D+",""));
			default_b = Double.parseDouble(in.readLine().replaceAll("\\D+",""));
			
			//2 comment lines
			in.readLine();
			in.readLine();
			
			noFunction= Integer.parseInt(in.readLine().replaceAll("\\D+",""));
			in.readLine();
			for (int i=0;i<noFunction;i++)
			{
				vnfNodeLst = new ArrayList<Integer>();
				double lamda= Double.parseDouble(in.readLine().split(" ")[1]);
				functionArr.add(new nFunction(i+1,lamda,vnfNodeLst));
			}
			in.readLine();
			in.readLine();
			for (int i=0;i <noVertex;i++)
			{
				double _cap = Double.parseDouble(in.readLine().split(" ")[1]);
	   	        cap.set(i,_cap);
			}
			for (int i=0;i<7;i++)
				in.readLine();
			st_temp = in.readLine();
			
			while (!st_temp.equals(";"))
			{
				int _node = Integer.parseInt(st_temp.split(" ")[0]);
				int _func = Integer.parseInt(st_temp.split(" ")[1]);
				nFunction _f = functionArr.get(_func-1);
				vnfNodeLst = _f.getVnfNode();
				vnfNodeLst.add(_node);
				double lamda= _f.getLamda();
				functionArr.set(_func-1,new nFunction(_func,lamda,vnfNodeLst));
				st_temp= in.readLine();
			}
			g= new nGraph(cap,w);
            // Always close files.
            in.close();  
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	
	
	}
	public static void ReadData(String fileName)
	{		
		File file = new File(fileName);
		functionArr = new ArrayList<nFunction>();
		DemandArray = new ArrayList<nDemand>();
		ArrayList<Integer> vnfNodeLst = new ArrayList<Integer>();
        try {
			in = new BufferedReader(new FileReader(file));
			//First line -> set of parameters
			String[] tempLine=in.readLine().split(" ");
			noVertex= Integer.parseInt(tempLine[0]);
			E = Integer.parseInt(tempLine[1]);
			noFunction= Integer.parseInt(tempLine[2]);
			prob = Double.parseDouble(tempLine[3]);
			//second line -> set of Functions
			for (int i=0;i<noFunction;i++)
			{
				vnfNodeLst = new ArrayList<Integer>();
				tempLine = in.readLine().split(";"); 
				double lamda= Double.parseDouble(tempLine[0]);
				String[] nodeLine = tempLine[1].split(" ");
				for(int j=0; j< nodeLine.length;j++)
					vnfNodeLst.add(Integer.parseInt(nodeLine[j]));
				functionArr.add(new nFunction(i+1,lamda,vnfNodeLst));
			}
			//luu vao mang noVertex+1 chieu
			
			Vector<Double> cap = new Vector<Double>(noVertex+1);
			ArrayList<List<Double>> w = new ArrayList<List<Double>>();			
			
			for (int i=0;i <noVertex;i++)
			{
				double _cap = Double.parseDouble(in.readLine());
	   	        cap.add(_cap);
			}
			
			for (int i=0;i<noVertex;i++)
			{
				ArrayList<Double> temp= new ArrayList<>();
				tempLine = in.readLine().split(" ");
				for(int j=0;j<noVertex;j++)
				{
					temp.add(Double.parseDouble(tempLine[j]));
				}
				w.add(temp);
			}
			g= new nGraph(cap,w);
            // Always close files.
            in.close();  
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	
	}
	public static double exponentialRandom(double mu)
	{
		Random r = new Random();
		ExponentialGenerator ex = new ExponentialGenerator(mu, r);
		System.out.println("Random value: "+ ex.nextValue());
		return ex.nextValue();
		
	}
	public static double poissonRandom(double lamda)
	{
		Random r = new Random();
		PoissonGenerator pois = new PoissonGenerator(lamda, r);
		System.out.println("Random poisson value: "+ pois.nextValue());
		return pois.nextValue();
	}
	
    public static double nextTime(double rateParameter)
    {
    	Random r = new Random();
    	return -Math.log(1.0 - r.nextDouble()) / rateParameter;
    }
    public static boolean test(double lamda,double processTime,String fileName,int NumFlow, String infile)
    {

    	double processingReq =0.05;
		int dem1=0;
		int dem2=0;
		noFunction=2;
		int noFInD=2;
		double arrivalTime=0.0;
		double now=0.0;
		int index=0;
		link_load= new double[noVertex][noVertex];
		//int id_temp=-1;
		ArrayList<Integer> id_temp = new ArrayList<>();
		ArrayList<Integer> sol=new ArrayList<>();
		//ArrayList<ArrayList<Integer>> newsol=new ArrayList<>();
		ArrayList<nOldDemand> processingLst = new ArrayList<>();
		
		ArrayList<ArrayList<nOldDemand>> all4ProcessingLst = new ArrayList<ArrayList<nOldDemand>>();
		//ArrayList<nGraph> all4g_edit= new ArrayList<nGraph>();
		
		ArrayList<Integer> acceptNoLst = new ArrayList<Integer>();
		ArrayList<Double> avgLenLst = new ArrayList<Double>();
		ArrayList<Double> maximumLinkLoad = new ArrayList<>();
		ArrayList<Double> runTime = new ArrayList<>();
		
		//random topology -> nGraph 
		
	    
		//random 10000 flows
	    int dem=NumFlow;
	    int idFlow=0;
	    Queue<Double> evenLst =  new LinkedList<Double>();
	    g_edit= new nGraph(g.cap, g.w);
	    for (int i=0;i<3;i++)
	    {
	    	//all4g_edit.add(g_edit);
	    	acceptNoLst.add(0);
	    	avgLenLst.add(0.0);
	    	all4ProcessingLst.add(null);
	    	maximumLinkLoad.add(0.0);
	    	runTime.add(0.0);
	    }
	    while (idFlow<dem)
	    {
	    	//random flow 1 ()
	    	evenLst.add(arrivalTime);
	    	arrivalTime = now + nextTime(lamda);    	

	    	now = arrivalTime;
	    	idFlow++;
	    }
	    try {
			File file = new File(fileName);
			out = new BufferedWriter(new FileWriter(file,true));
			while (!evenLst.isEmpty())
		    {
				
		    	now=evenLst.poll();//xet thoi diem den cua package;
		    	nDemand _d = new nDemand(idFlow, 1,6, functionArr,noFInD,now,processTime,processingReq);
		    	System.out.println("Flow: "+ index+":"+_d.getSrc()+","+_d.getDest() );
		    	for(int i=0;i<3;i++)
		    	{
		    		fl = false;
		    		//newsol = new ArrayList<>();
		    		sol= new ArrayList<>();
		    		id_temp= new ArrayList<>();
		    		if(all4ProcessingLst.size()>0)
		    			processingLst = all4ProcessingLst.get(i);
		    		else
		    			processingLst =new ArrayList<>();
		    		//g_edit = all4g_edit.get(i);
		    		g_edit= new nGraph(g.cap, g.w);
		    		for (int i1=0;i1<noVertex;i1++)
						for (int i2=0;i2<noVertex;i2++)
							link_load[i1][i2]=0.0000000000000;
		    		if(processingLst!=null && processingLst.size()>0)
			    	{
			    		for(nOldDemand _old: processingLst)
			    		{
			    			
			    			if(now > (_old.GetArrivalTime()+_old.GetProcessTime()))
			    			{
			    				id_temp.add(processingLst.indexOf(_old));						
			    			}
			    			else
			    			{
			    				ArrayList<Integer> path= _old.Get_path();
			    				
			    					for (int _node=0;_node<path.size()-1;_node++)
									{
			    						if(path.get(_node)!=path.get(_node+1))
			    						{
			    							double w_temp= g_edit.getEdgeWeight(path.get(_node), path.get(_node+1))-_old.GetBandwidth();
											g_edit.setEdgeWeight(path.get(_node), path.get(_node+1),w_temp );
				    						if(g.getEdgeWeight(path.get(_node), path.get(_node+1))>0)
				    							link_load[path.get(_node)-1][path.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(path.get(_node), path.get(_node+1));
				    						
				    						
			    						}		    						
			    						
									}
			    					for (int _node=0;_node<path.size();_node++)
			    					{
			    						double c_temp= g_edit.getCap(path.get(_node))-_old.GetProcessReq();
										g_edit.setCap(path.get(_node),c_temp );
			    					}
			    				ArrayList<Pair> funLoc1 = _old.Get_funLoc();
			    				for (int j=0;j<funLoc1.size();j++)
		    					{
		    						Pair pr = funLoc1.get(j);

				    				for (int iF=0;iF<_d.getFunctions().size();iF++)
				    				{
				    					if(pr.getfunction() == _d.getFunctions().get(iF))
			    						{
			    							double mul = getFunction(_d.getFunctions().get(iF)).getLamda();
			    							double c_temp= g_edit.getCap(pr.getnode())-mul;
		    								g_edit.setCap(pr.getnode(),c_temp );
			    							
			    						}
				    				}
		    						
		    					}
			    				
			    			}
			    		}
			    	}
		    		else
		    			processingLst= new ArrayList<>();
		    		if(id_temp.size()>0)
		    		{
		    			for (int j=0;j<id_temp.size();j++)
		    				processingLst.remove(id_temp.get(j));
		    		}
		    		final long startTime = System.currentTimeMillis();
		    			
		    		switch (i+1) {
					case 1:
						sol = GreedyForward(_d,g_edit);
						break;
					case 2:
						sol = OptimalSimpleGraph(_d,g_edit);
						if(flag==1)
							dem1++;
						if(flag==2)
							dem2++;
						break;
					case 3:
						sol = optimal(_d,g_edit);
						break;
					default:
						break;
					}
		    		_duration = System.currentTimeMillis() - startTime;
		    		runTime.set(i, runTime.get(i)+_duration);
		    		if(fl)
			    	{
		    			if(sol!=null && sol.size()>0)
		    			{	    				
			    			acceptNoLst.set(i, acceptNoLst.get(i)+1);
			    			avgLenLst.set(i, avgLenLst.get(i)+sol.size());
				    		nOldDemand _old = new nOldDemand(index, now, processTime, _d.getBw(), sol, funLoc,_d.getProcessReq());
				    		processingLst.add(_old);
				    		System.out.print(i+":[");
		    				for (int _node=0;_node<sol.size()-1;_node++)
							{
		    					System.out.print(sol.get(_node)+" ");
	    						if(g.getEdgeWeight(sol.get(_node), sol.get(_node+1))>0)
	    							link_load[sol.get(_node)-1][sol.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(sol.get(_node), sol.get(_node+1));
	    						
							}
		    				System.out.print(sol.get(sol.size()-1)+" ");
		    				System.out.print("]");
		    				System.out.println();
		    			}
			    		maxlinkload =maximumLinkLoad.get(i);
			    		for (int i1=0;i1<noVertex;i1++)
							for (int i2=0;i2<noVertex;i2++)
								if(link_load[i1][i2]>maxlinkload)
									maxlinkload = link_load[i1][i2];
			    		System.out.println("max: "+ maxlinkload);
			    		maximumLinkLoad.set(i, maxlinkload);
			    		all4ProcessingLst.set(i, processingLst);
			    	}

		    		
		    		//all4g_edit.set(i, g_edit);
		    	}
		    	index++;
		    	//System.out.println("number of processed flows: "+ index);
		    }
			
			out.write(infile+" "+ NumFlow+" "+ processTime+" "+lamda +" "+ prob+ " ");
			for (int i=0;i<3;i++)
			{
				double blocking= 1-1.0*acceptNoLst.get(i)/NumFlow;
				out.write(blocking+" "+ avgLenLst.get(i)/acceptNoLst.get(i)+ " " + maximumLinkLoad.get(i)+ " "+runTime.get(i)/NumFlow+" ");
				if(i==1)
					out.write(dem1*1.0/NumFlow+" " +1.0*dem2/NumFlow+" ");
			}
			out.newLine();
		    }
			catch ( IOException e1 ) {
				e1.printStackTrace();
				} finally {
					if ( out != null )
						try {
							out.close();
							} catch (IOException e) {
								e.printStackTrace();}
					}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
		
	    
		return true;
	
    
    
    }
    public static boolean simulation_final(double lamda,double mu,String fileName,double NumFlow, String infile, int idAlg,int noFInD)
    {

    	double epsilon = 0.01;
    	double X = NumFlow;
    	double processingReq =0.05;
		int dem1=0;
		int dem2=0;
		noFunction=10;
		double now=0.0;
		int index=0;
		link_load= new double[noVertex][noVertex];
		//int id_temp=-1;
		ArrayList<Integer> id_temp = new ArrayList<>();
		ArrayList<Integer> sol=new ArrayList<>();
		//ArrayList<ArrayList<Integer>> newsol=new ArrayList<>();
		ArrayList<nOldDemand> processingLst = new ArrayList<>();
		
		
		//ArrayList<nGraph> all4g_edit= new ArrayList<nGraph>();
		
		int acceptNoLst = 0;
		double avgLenLst = 0.0;
		double maximumLinkLoad = 0.0;
		double runTime =0.0;
		double finalblocking = 0.0;
		double finallengLst = 0.0;
		double finalRunTime = 0.0; 
		
		//random topology -> nGraph 
		
		//random 10000 flows
	    int idFlow=0;
	    int flows=0;
	    g_edit= new nGraph(g.cap, g.w);
	    double warmup = 100;
	    
	    try {
			File file = new File(fileName);
			out = new BufferedWriter(new FileWriter(file,true));
			while (true)
		    {
				flag =0;
				double processTime = exponentialRandom(mu);
		    	nDemand _d = new nDemand(idFlow, g.getV(), functionArr,noFInD,now,processTime,processingReq);
		    	System.out.println("Flow: "+ index+":"+now+":"+ _d.getSrc()+","+_d.getDest() );
		    		fl = false;
		    		//newsol = new ArrayList<>();
		    		sol= new ArrayList<>();
		    		id_temp= new ArrayList<>();
		    		g_edit= new nGraph(g.cap, g.w);
		    		for (int i1=0;i1<noVertex;i1++)
						for (int i2=0;i2<noVertex;i2++)
							link_load[i1][i2]=0.0000000000000;
		    		if(processingLst!=null && processingLst.size()>0)
			    	{
			    		for(nOldDemand _old: processingLst)
			    		{
			    			
			    			if(now > (_old.GetArrivalTime()+_old.GetProcessTime()))
			    			{
			    				id_temp.add(processingLst.indexOf(_old));						
			    			}
			    			else
			    			{
			    				ArrayList<Integer> path= _old.Get_path();
			    				
			    					for (int _node=0;_node<path.size()-1;_node++)
									{
			    						if(path.get(_node)!=path.get(_node+1))
			    						{
			    							double w_temp= g_edit.getEdgeWeight(path.get(_node), path.get(_node+1))-_old.GetBandwidth();
											g_edit.setEdgeWeight(path.get(_node), path.get(_node+1),w_temp );
				    						if(g.getEdgeWeight(path.get(_node), path.get(_node+1))>0)
				    							link_load[path.get(_node)-1][path.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(path.get(_node), path.get(_node+1));
				    						
				    						
			    						}		    						
			    						
									}
			    					for (int _node=0;_node<path.size();_node++)
			    					{
			    						double c_temp= g_edit.getCap(path.get(_node))-_old.GetProcessReq();
										g_edit.setCap(path.get(_node),c_temp );
			    					}
			    				ArrayList<Pair> funLoc1 = _old.Get_funLoc();
			    				for (int j=0;j<funLoc1.size();j++)
		    					{
		    						Pair pr = funLoc1.get(j);

				    				for (int iF=0;iF<_d.getFunctions().size();iF++)
				    				{
				    					if(pr.getfunction() == _d.getFunctions().get(iF))
			    						{		    								
		    								double mul = getFunction(_d.getFunctions().get(iF)).getLamda();
			    							double c_cap =  g_edit.getCap(pr.getnode())-mul;
			    							double c_temp= Math.round(100000 *c_cap)/100000.0 ;
		    								g_edit.setCap(pr.getnode(),c_temp );
			    							
			    						}
				    				}
		    						
		    					}
			    				
			    			}
			    		}
			    	}
		    		else
		    			processingLst= new ArrayList<>();
		    		nOldDemand  nOld = new nOldDemand();
		    		if(id_temp.size()>0)
		    		{
		    			for (int j=id_temp.size()-1;j>=0;j--)
		    			{
		    				int index_remove= id_temp.get(j);
		    				nOld=processingLst.remove(index_remove);
		    			}
		    		}
		    		final long startTime = System.currentTimeMillis();
		    			
		    		switch (idAlg) {
					case 1:
						sol = GreedyForward(_d,g_edit);
						break;
					case 2:
						sol = OptimalSimpleGraph(_d,g_edit);
						
						break;
					case 3:
						sol = optimal(_d,g_edit);
						break;
					case 4:
						sol = noFunctionAlg(_d,g_edit);
						break;
					default:
						break;
					}
		    		_duration = System.currentTimeMillis() - startTime;
		    		
		    		if(now>warmup)
		    		{
		    			flows++;
		    			runTime+=_duration;
		    			if(idAlg==2)
		    			{

			    			if(flag==1)
								dem1++;
							if(flag==2)
								dem2++;
		    			}
		    		}
		    		if(fl)
			    	{
		    			if(sol!=null && sol.size()>0)
		    			{	
		    				if(now>warmup)
		    				{
		    					acceptNoLst+=1;
				    			avgLenLst+=sol.size();
		    				}
			    			
				    		nOldDemand _old = new nOldDemand(index, now, processTime, _d.getBw(), sol, funLoc,_d.getProcessReq());
				    		processingLst.add(_old);
		    				for (int _node=0;_node<sol.size()-1;_node++)
							{
		    					System.out.print(sol.get(_node)+" ");
	    						if(g.getEdgeWeight(sol.get(_node), sol.get(_node+1))>0)
	    							link_load[sol.get(_node)-1][sol.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(sol.get(_node), sol.get(_node+1));
	    						
							}
		    				System.out.print(sol.get(sol.size()-1)+" ");
		    				System.out.print("]");
		    				System.out.println();
		    			}
			    		for (int i1=0;i1<noVertex;i1++)
							for (int i2=0;i2<noVertex;i2++)
								if(link_load[i1][i2]>maxlinkload)
									maxlinkload = link_load[i1][i2];
			    		System.out.println("max: "+ maxlinkload);
			    		maximumLinkLoad=maxlinkload ;
			    	}

		    	
		    	index++;
		    	//System.out.println("number of processed flows: "+ index);
		    	now = now+ nextTime(lamda);
		    	if(now > X)
		    	{
			    	finalblocking= 1.0 - acceptNoLst*1.0/flows;
			    	finallengLst=avgLenLst/acceptNoLst;
			    	finalRunTime= runTime/flows;
		    		break;
		    	}
		    }
			
			out.write("Alg"+idAlg+" "+infile+" "+ NumFlow+" "+ lamda +" "+ prob+" "+ finalblocking+" "+ finallengLst+ " " + maximumLinkLoad+ " "+finalRunTime+" ");
			if(idAlg==2)
				out.write(dem1*1.0/flows+" " +1.0*dem2/flows+" ");			
			out.newLine();
		    }
			catch ( IOException e1 ) {
				e1.printStackTrace();
				} finally {
					if ( out != null )
						try {
							out.close();
							} catch (IOException e) {
								e.printStackTrace();}
					}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
		
	    
		return true;
	
    }
    
    public static boolean simulation_subgradien(double lamda,double mu,String fileName,double NumFlow, String infile,int algID,double delPar, int noFInD)
    {
    	double epsilon = 0.01;
    	double X = NumFlow;
    	double processingReq =0.05;
		int dem1=0;
		int dem2=0;
		noFunction=10;
		double now=0.0;
		int index=0;
		link_load= new double[noVertex][noVertex];
		//int id_temp=-1;
		ArrayList<Integer> id_temp = new ArrayList<>();
		ArrayList<Integer> sol=new ArrayList<>();
		//ArrayList<ArrayList<Integer>> newsol=new ArrayList<>();
		ArrayList<nOldDemand> processingLst = new ArrayList<>();
		
		
		//ArrayList<nGraph> all4g_edit= new ArrayList<nGraph>();
		
		int acceptNoLst = 0;
		double avgLenLst = 0.0;
		double maximumLinkLoad = 0.0;
		double runTime =0.0;
		double finalblocking = 0.0;
		double finallengLst = 0.0;
		double finalRunTime = 0.0; 
		
		//random topology -> nGraph 
		
		//random 10000 flows
	    int idFlow=0;
	    int flows=0;
	    g_edit= new nGraph(g.cap, g.w);
	    double warmup = 100;
	    try {
			File file = new File(fileName);
			out = new BufferedWriter(new FileWriter(file,true));
			while (true)
		    {
				flag =0;
				double processTime = exponentialRandom(mu);
		    	nDemand _d = new nDemand(idFlow++, g.getV(), functionArr,noFInD,now,processTime,processingReq);
		    	System.out.println("Flow: "+ index+":"+now+":"+_d.getSrc()+","+_d.getDest() );
		    		fl = false;
		    		//newsol = new ArrayList<>();
		    		sol= new ArrayList<>();
		    		id_temp= new ArrayList<>();
		    		g_edit= new nGraph(g.cap, g.w);
		    		for (int i1=0;i1<noVertex;i1++)
						for (int i2=0;i2<noVertex;i2++)
							link_load[i1][i2]=0.0;
		    		if(processingLst!=null && processingLst.size()>0)
			    	{
			    		for(nOldDemand _old: processingLst)
			    		{
			    			
			    			if(now > (_old.GetArrivalTime()+_old.GetProcessTime()))
			    			{
			    				id_temp.add(processingLst.indexOf(_old));						
			    			}
			    			else
			    			{
			    				ArrayList<Integer> path= _old.Get_path();
			    				
			    					for (int _node=0;_node<path.size()-1;_node++)
									{
			    						if(path.get(_node)!=path.get(_node+1))
			    						{
			    							double w_temp= g_edit.getEdgeWeight(path.get(_node), path.get(_node+1))-_old.GetBandwidth();
											g_edit.setEdgeWeight(path.get(_node), path.get(_node+1),w_temp );
				    						if(g.getEdgeWeight(path.get(_node), path.get(_node+1))>0)
				    							link_load[path.get(_node)-1][path.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(path.get(_node), path.get(_node+1));
				    						
				    						
			    						}		    						
			    						
									}
			    					for (int _node=0;_node<path.size();_node++)
			    					{
			    						double c_temp= g_edit.getCap(path.get(_node))-_old.GetProcessReq();
										g_edit.setCap(path.get(_node),c_temp );
			    					}
			    				ArrayList<Pair> funLoc1 = _old.Get_funLoc();
			    				for (int j=0;j<funLoc1.size();j++)
		    					{
		    						Pair pr = funLoc1.get(j);

				    				for (int iF=0;iF<_d.getFunctions().size();iF++)
				    				{
				    					if(pr.getfunction() == _d.getFunctions().get(iF))
			    						{
			    							double mul = getFunction(_d.getFunctions().get(iF)).getLamda();
			    							double c_cap =  g_edit.getCap(pr.getnode())-mul;
			    							double c_temp= Math.round(100000 *c_cap)/100000.0 ;
		    								g_edit.setCap(pr.getnode(),c_temp );
			    							
			    						}
				    				}
		    						
		    					}
			    				
			    			}
			    		}
			    	}
		    		else
		    			processingLst= new ArrayList<>();
		    		nOldDemand nOld = new nOldDemand();
		    		if(id_temp.size()>0)
		    		{
		    			for (int j=id_temp.size()-1;j>=0;j--)
		    			{
		    				int index_remove= id_temp.get(j);
		    				nOld=processingLst.remove(index_remove);
		    			}
		    		}
		    		final long startTime = System.currentTimeMillis();
		    		
		    		switch (algID) {
					case 1:
						sol = A_1(_d,g_edit);
						break;
					case 2:
						sol = A_2(_d,g_edit);
						
						break;
					case 3:
						sol = B_1(_d,g_edit);
						break;
					case 4:
						sol = B_2(_d,g_edit,delPar);
						break;
					case 5:
						sol = B_1Fake(_d,g_edit);
						break;
					case 6:
						sol = B_2Fake(_d,g_edit,delPar);
						break;
					default:
						break;
					}
		    		
		    		_duration = System.currentTimeMillis() - startTime;
		    		
		    		if(now>warmup)
		    		{
		    			flows++;
		    			runTime+=_duration;
		    			if(flag==1)
							dem1++;
						if(flag==2 )
							dem2++;
		    		}
		    		if(fl)
			    	{
		    			if(sol!=null && sol.size()>0)
		    			{	
		    				if(now>warmup)
		    				{
		    					acceptNoLst+=1;
				    			avgLenLst+=sol.size();
		    				}
			    			
				    		nOldDemand _old = new nOldDemand(index, now, processTime, _d.getBw(), sol, funLoc,_d.getProcessReq());
				    		processingLst.add(_old);
		    				for (int _node=0;_node<sol.size()-1;_node++)
							{
		    					System.out.print(sol.get(_node)+" ");
	    						if(g.getEdgeWeight(sol.get(_node), sol.get(_node+1))>0)
	    							link_load[sol.get(_node)-1][sol.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(sol.get(_node), sol.get(_node+1));
	    						
							}
		    				System.out.print(sol.get(sol.size()-1)+" ");
		    				System.out.print("]");
		    				System.out.println();
		    			}
			    		for (int i1=0;i1<noVertex;i1++)
							for (int i2=0;i2<noVertex;i2++)
								if(link_load[i1][i2]>maxlinkload)
									maxlinkload = link_load[i1][i2];
			    		System.out.println("max: "+ maxlinkload);
			    		maximumLinkLoad=maxlinkload ;
			    	}

		    	
		    	index++;
		    	//System.out.println("number of processed flows: "+ index);
		    	now = now+ nextTime(lamda);
		    	if(now > X)
		    	{
			    	finalblocking= 1.0 - acceptNoLst*1.0/flows;
			    	finallengLst=avgLenLst/acceptNoLst;
			    	finalRunTime= runTime/flows;
		    		break;
		    	}
		    }
			
			out.write("Alg_Subgradient "+infile+" "+ NumFlow+" "+ lamda +" "+ prob+" "+ finalblocking+" "+ finallengLst+ " " + maximumLinkLoad+ " "+finalRunTime+" ");
			if (algID ==1 || algID ==3 || algID==5)
				out.write(dem1*1.0/flows+" " +1.0*dem2/flows);			
			out.newLine();
		    }
			catch ( IOException e1 ) {
				e1.printStackTrace();
				} finally {
					if ( out != null )
						try {
							out.close();
							} catch (IOException e) {
								e.printStackTrace();}
					}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
		
	    
		return true;
	
    
    
    
    
    
    
    }
	public static void readDataReal(String filePara)
	{
		BufferedReader in;
		File file = new File(filePara);
        try {
			in = new BufferedReader(new FileReader(file));
			String strLine = in.readLine();
			int dataNo= Integer.parseInt(strLine);
			dataReal = new Vector<Vector<Double>>();
			for (int i=0;i<dataNo;i++)
			{
				//doc n hang tiep theo
				strLine = in.readLine();
				String[] _line = strLine.split(" ");
				Vector<Double> t= new Vector<Double>(4);
				for (int j=0;j <4;j++)
				{
					t.addElement(Double.parseDouble(_line[j]));
				}
				dataReal.addElement(t);
			}
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void mainCheckDiameter (String[] args)
	{


		//BufferedWriter out1 = null;
		
		noFunction=10;
		int lamda=Integer.parseInt(args[0]);
		double processingTime = Double.parseDouble(args[1]);
		String fileName = args[2];
		//int numFlow=Integer.parseInt(args[3]);
		double numFlow = Double.parseDouble(args[3]);
		String dirPath = args[4];
		int algId=Integer.parseInt(args[5]);
		File dir = new File(dirPath);
		String[] extensions = new String[] { "txt" };
		@SuppressWarnings("unchecked")
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);

		
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					System.out.println("lambda: "+ lamda);
					int diameter = computeDiameter(file.getPath());
					System.out.println("diameter:::::" + diameter);
					
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
	
	
	}
	public static void mainCC(String[] args)//main chinh de chay simulation
	{

		//BufferedWriter out1 = null;
		
		noFunction=10;
		int lamda=Integer.parseInt(args[0]);
		double processingTime = Double.parseDouble(args[1]);
		String fileName = args[2];
		//int numFlow=Integer.parseInt(args[3]);
		double numFlow = Double.parseDouble(args[3]);
		String dirPath = args[4];
		int algId=Integer.parseInt(args[5]);
		double delPar = Double.parseDouble(args[6]);
		int NoIdF=Integer.parseInt(args[7]);
		File dir = new File(dirPath);
		String[] extensions = new String[] { "txt" };
		@SuppressWarnings("unchecked")
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);

		
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					System.out.println("lambda: "+ lamda);
					ReadData(file.getPath());
					//simulation_final(lamda,processingTime,fileName,numFlow,file.getPath(),algId,NoIdF);
					simulation_subgradien(lamda,processingTime,fileName,numFlow,file.getPath(),algId,delPar,NoIdF);
//					for (int i=0;i<20;i++)
//					{
//						
//						exponentialRandom(0.2);// rate = 1/mean
//						poissonRandom(10.0);
//					}
					
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
	
	}

	public static void mainI(String[] args) {
	int NoFun =4;
	int NoNode=4;
	int capa=1;
	double p = 0.7;
	WriteData(6,20, NoFun,p,"test.txt",NoNode,capa);
}
	public static void mainii(String[] args)
	{
		int noVer = Integer.parseInt(args[0]);
		int NoFun = Integer.parseInt(args[1]);
		double p = 0.025;
		for (int i=0;i<13;i++)
		{
			int j=i+1;
			String fileName = "input"+ j+".txt";
			CreateInput(noVer, NoFun, p, fileName, 20, 3, 2, 0.1);
			p+=0.003;
		}
		
	}
	
	public static boolean runSimulation(double lamda,double mu,String fileName,double NumFlow, String infile,int algID,double delPar, int noFInD)
	{
//Chay simulation voi do thi nho. Khi nao on dinh, thi random 1 so cac connection va prints 1. network, 2. solution
    	String fileName1= fileName;
		//int numberExtracts = UtilizeFunction.randInt(100, 150);
    	int numberExtracts = 100;
		int countNumber = 0;
		double epsilon = 0.01;
    	double X = NumFlow;
    	int Xint= (int)lamda * 6990;
    	int rand = (int) ((int)lamda *(X+100));
    	double processingReq =0.05;
		int dem1=0;
		int dem2=0;
		double now=0.0;
		int index=0;
		link_load= new double[noVertex][noVertex];
		//int id_temp=-1;
		ArrayList<nOldDemand> id_temp = new ArrayList<>();
		ArrayList<Integer> sol=new ArrayList<>();
		//ArrayList<ArrayList<Integer>> newsol=new ArrayList<>();
		ArrayList<nOldDemand> processingLst = new ArrayList<>();
		
		ArrayList<Integer> listNode = new ArrayList<>();
		System.out.println("number:"+rand +","+Xint);
		for (int i =0;i<600;i++)
		{
			
			int r = UtilizeFunction.randInt(rand, Xint);
			while (listNode.contains(r))
			{
				r = UtilizeFunction.randInt(rand, Xint);				
			}
			listNode.add(r);
		}
		
		//ArrayList<nGraph> all4g_edit= new ArrayList<nGraph>();
		
		int acceptNoLst = 0;
		double avgLenLst = 0.0;
		double maximumLinkLoad = 0.0;
		double runTime =0.0;
		double finalblocking = 0.0;
		double finallengLst = 0.0;
		double finalRunTime = 0.0; 
		String _folder = "";
		
		//random topology -> nGraph 
		
		//random 10000 flows
	    int idFlow=0;
	    int flows=0;
	    g_edit= new nGraph(g.cap, g.w);
	    double warmup = 400;
	    
	    try {
			File file = new File(fileName);
			out = new BufferedWriter(new FileWriter(file,true));
			while (true)
		    {
				
				
				flag =0;
				double processTime = exponentialRandom(mu);
				
				//noFInD = noFunction;
		    	nDemand _d = new nDemand(idFlow++, g.getV(), functionArr,noFInD,now,processTime,processingReq);
		    	System.out.println("Flow: "+ index+":now = "+now+": processTime = "+processTime + ": "+_d.getSrc()+","+_d.getDest() );
		    		fl = false;
		    		//newsol = new ArrayList<>();
		    		sol= new ArrayList<>();
		    		id_temp= new ArrayList<>();
		    		g_edit= new nGraph(g.cap, g.w);
		    		for (int i1=0;i1<noVertex;i1++)
						for (int i2=0;i2<noVertex;i2++)
							link_load[i1][i2]=0.0;
		    		if(processingLst!=null && processingLst.size()>0)
			    	{
		    			System.out.println("Before Number of processing connections: "+ processingLst.size());
			    		for(nOldDemand _old: processingLst)
			    		{
			    			double time_old = _old.GetArrivalTime()+_old.GetProcessTime();
			    			
			    			if(now > time_old)
			    			{
			    				System.out.println("Ended: "+ time_old);
			    				id_temp.add(_old);						
			    			}
			    			else
			    			{
			    				//System.out.println("Not ended: "+ time_old);
			    				ArrayList<Integer> path= _old.Get_path();
			    				

			    				for (int i=0;i<path.size()-1;i++)
			    				{
			    					int _srcNode = path.get(i);
			    					int _destNode = path.get(i+1);
			    					double _w = g_edit.getEdgeWeight(_srcNode, _destNode)-_d.getBw();
			    					double c_temp= Math.round(100000 *_w)/100000.0 ;
			    					if(c_temp<0)
			    					{
			    						
			    						System.out.println("BI SAI 1....");
			    					}
			    					else
			    					{
			    						g_edit.setEdgeWeight(_srcNode, _destNode, c_temp);
			    						if(g.getEdgeWeight(_srcNode, _destNode)>0)
			    							link_load[_srcNode-1][_destNode-1]+=_old.GetBandwidth()/g.getEdgeWeight(_srcNode,_destNode);
			    					}
			    					
			    						
			    				}
			    				
			    				for(int i = 0;i<path.size();i++)
			    				{
			    					int _node = path.get(i);
			    					double _c= g_edit.getCap(_node) - _d.getProcessReq();
			    					double c_temp= Math.round(100000 *_c)/100000.0 ;
			    					if(c_temp<0)
			    					{
			    						System.out.println("BI SAI 22222");
			    					}
			    					else
			    					{
			    						g_edit.setCap(_node, c_temp);
			    					}
			    				}
			    				
			    				
			    				ArrayList<Pair> funLoc1 = _old.Get_funLoc();
			    				for (int j=0;j<funLoc1.size();j++)
		    					{
			    					Pair _pair = funLoc1.get(j);
			    					int _node = _pair.getnode();
			    					int _func = _pair.getfunction();
			    					double _c = g_edit.getCap(_node) - getFunction(_func).getLamda();
			    					double c_temp= Math.round(100000 *_c)/100000.0 ;
			    					if(c_temp<0)
			    					{
			    						System.out.println("SAI KINH DI");
			    					}
			    					else
			    						g_edit.setCap(_node, c_temp);
			    					
			    					
		    						
		    						
		    					}
			    				
			    			}
			    		}
			    	}
		    		else
		    			processingLst= new ArrayList<>();
		    		System.out.println("Number of processing connections: "+ processingLst.size());
		    		if(id_temp.size()>0)
		    		{
		    			for (nOldDemand _O : id_temp)
		    			{
		    				processingLst.remove(_O);
		    			}
		    			
		    		}
		    		final long startTime = System.currentTimeMillis();
		    		
		    		 nGraph g_save= new nGraph(g_edit.cap, g_edit.w);
		    		
		    		switch (algID) {
					case 1:
						_folder = "MH1//";
						sol = A_1(_d,g_edit);
						break;
					case 2:
						_folder = "MH2//";
						sol = A_2(_d,g_edit);
						
						break;
					case 3:
						_folder = "SG1//";
						sol = B_1(_d,g_edit);
						break;
					case 4:
						_folder = "SG2//";
						sol = B_2(_d,g_edit,delPar);
						break;
					case 5:
						sol = B_1Fake(_d,g_edit);
						break;
					case 6:
						sol = B_2Fake(_d,g_edit,delPar);
						break;
					default:
						break;
					}
		    		
		    		_duration = System.currentTimeMillis() - startTime;
		    		
		    		if(now>warmup)
		    		{
		    			flows++;
		    			runTime+=_duration;
		    			if(flag==1)
							dem1++;
						if(flag==2 )
							dem2++;
		    		}
		    		if(fl)
			    	{
		    			if(sol!=null && sol.size()>0)
		    			{	
		    				if(now>warmup)
		    				{
		    					acceptNoLst+=1;
				    			avgLenLst+=sol.size();
		    				}
			    			
				    		nOldDemand _old = new nOldDemand(index, now, processTime, _d.getBw(), sol, funLoc,_d.getProcessReq());
				    		processingLst.add(_old);
		    				for (int _node=0;_node<sol.size()-1;_node++)
							{
		    					System.out.print(sol.get(_node)+" ");
	    						if(g.getEdgeWeight(sol.get(_node), sol.get(_node+1))>0)
	    							link_load[sol.get(_node)-1][sol.get(_node+1)-1]+=_old.GetBandwidth()/g.getEdgeWeight(sol.get(_node), sol.get(_node+1));
	    						
							}
		    				System.out.print(sol.get(sol.size()-1)+" ");
		    				System.out.print("]");
		    				System.out.println();
		    			}
			    		for (int i1=0;i1<noVertex;i1++)
							for (int i2=0;i2<noVertex;i2++)
								if(link_load[i1][i2]>maxlinkload)
									maxlinkload = link_load[i1][i2];
			    		System.out.println("max: "+ maxlinkload);
			    		maximumLinkLoad=maxlinkload ;
			    	}

		    	
		    	index++;
		    	//System.out.println("number of processed flows: "+ index);
		    	now = now+ nextTime(lamda);
		    
		    	if(now > X && now <7000)
		    	{
		    		if(listNode.contains(index) )
		    		{
		    			//In ra network truoc + solution
		    			//in network voi demand
		    			
		    			DecimalFormat df = new DecimalFormat("#.####");
		    			BufferedWriter out1;
		    			countNumber++;
		    			fileName1 = _folder+"graph_"+countNumber+"_" +fileName; 
		    			fileName1 = fileName1.replace("output", "");
		    			
				    	        try {  
				    	        	out1= new BufferedWriter(new FileWriter(fileName1));
				    			    //ghi ra file
				    			    
				    			    out1.write ("#\r\n");
				    			    out1.write ("# Test data\r\n");
				    			    out1.write ("#\r\n");
				    			    out1.write("param p_no_nodes :=" + noVertex +";\r\n");
				    			    out1.write("set p_links := \r\n");
				    			    for (int i=0;i<g_save.getV();i++)
				    			    {
				    			    	for(int j=0;j<g_save.getV();j++)
				    			    	{
				    			    		if(i!=j && g_save.getEdgeWeight(i+1, j+1)>0)
				    			    			out1.write((i+1) + " "+ (j+1)+ "\r\n");
				    			    	}
				    			    }
				    			    out1.write(";\r\n");
				    			    out1.write("param C :=\r\n");
				    			    for (int i=0;i<g_save.getV();i++)
				    			    {
				    			    	for(int j=0;j<g_save.getV();j++)
				    			    	{
				    			    		if(i!=j && g_save.getEdgeWeight(i+1, j+1)>0)
				    			    			out1.write((i+1) + " "+ (j+1) +" "+ g_save.getEdgeWeight(i+1, j+1)+ "\r\n");
				    			    	}
				    			    }
				    			    out1.write(";\r\n");
				    			    int ori = _d.getSrc();
				    			    int dest = _d.getDest();
				    			    default_b = _d.getBw();
				    			    default_p = _d.getProcessReq();
				    			    out1.write("param origin := " + ori+ ";\r\n");
				    			    out1.write("param dest :=" + dest + ";\r\n");
				    			    out1.write("#\r\n");
				    			    out1.write("# These 2 parameters are the values of b and p of the paper\r\n");
				    			    out1.write("param default_p := "+default_p +";\r\n");
				    			    out1.write("param default_b := "+ default_b+";\r\n");
				    			    out1.write("#\r\n");
				    			    out1.write("#\r\n");
				    			    
				    			    out1.write("param tot_no_functions := "+ functionArr.size() + ";\r\n");
				    			    
				    			    out1.write("set f_used :=");
				    			    for (int i=0;i<_d.getNoF();i++)
				    			    {
				    			    	int f_id = _d.getFunctions().get(i);
				    			    	out1.write(" "+ f_id);
				    			    }
				    			    out1.write(";\r\n");
				    			    
				    			    
				    			    //out1.write("param no_functions := "+ _d.getNoF() + ";\r\n");
				    			    out1.write("param q := \r\n");
				    			    for (int i=0;i<_d.getNoF();i++)
				    			    {
				    			    	int f_id = _d.getFunctions().get(i);
				    		               out1.write((i+1) + " "+ df.format(getFunction(f_id).getLamda())+"\r\n");
				    			    }
				    			    out1.write(";\r\n");
				    			    
				    			    out1.write("param P := \r\n");
				    			    for (int i=0;i<g_save.getV();i++)
				    			    {
				    			    	if(g_save.getCap(i+1)>0)
				    		               out1.write(i+1 + " "+ df.format(g_save.getCap(i+1))+"\r\n");
				    			    	else
				    			    		out1.write(i+1 + " 0.01\r\n");
				    			    }
				    			    out1.write(";\r\n");
				    			    
				    			    out1.write("#\r\n");
				    			    out1.write("#  This is the incidence matrix for functions and nodes \r\n");
				    			    out1.write("#  f_nodes[i,k] = 1 if node i contains function k \r\n");
				    			    out1.write ("#  Only the elements with value 1 need be given.\r\n");
				    			    out1.write("#\r\n");
				    			    
				    			    out1.write("param: f_nodes :=\r\n");
				    			    for (int j=0;j<_d.getNoF();j++)
				    			    {
				    			    	int f_id = _d.getFunctions().get(j);
				    			    	for (Integer _i : getFunction(f_id).getVnfNode()) 
					    			    {			    			    	
					    			    	for(int i=0;i<g_save.getV();i++)
					    			    	{
				    			            	if(_i == i+1)   
				    			            		out1.write(_i+" "+(j+1)+" 1\r\n" );
				    						}
					    			    }
				    			    }
				    			    out1.write(";");
				    			    out1.close();
				    				} catch (IOException e) {
				    				e.printStackTrace();
				    			}
				    			
				    			
						        try {
						        	if(fl && sol !=null && sol.size()>0)
						        	{
						        		fileName1 = fileName1.replace("graph", "solution");
						        	}
						        	else
						        		fileName1 = fileName1.replace("graph", "blockedConnection");
						        	out1= new BufferedWriter(new FileWriter(fileName1));
						        	
						        	if(fl&& sol !=null && sol.size()>0)
						        	{
							        	for(int i=0;i<copyLinks.size();i++)
							        	{
							        		ArrayList<Pair> _t = copyLinks.get(i);
							        		out1.write((i+1)+": ");
							        		System.out.print((i+1)+" ");
							        		for(int j=0;j<_t.size();j++)
							        		{
							        			out1.write("("+_t.get(j).getnode()+","+_t.get(j).getfunction()+") ");
							        			System.out.print("("+_t.get(j).getnode()+","+_t.get(j).getfunction()+") ");
							        		}
							        		System.out.println();
							        		out1.newLine();
							        	}
							        	
						        	}
						        	else
						        	{
						        		out1.write("This connection "+ idFlow + "is blocked");
						        	}
						        	
						        	
						        	 out1.close();
								} catch (IOException e1) {
								e1.printStackTrace();
							}  
		    		
		    		}
//		    		else
//		    		{
//		    			finalblocking= 1.0 - acceptNoLst*1.0/flows;
//		    			finallengLst=avgLenLst/acceptNoLst;
//		    			finalRunTime= runTime/flows;
//			    	
//		    			break;
//		    		}
		    		
		    	}
		    	else
		    	{
		    		if(now>X)
		    		{
		    			finalblocking= 1.0 - acceptNoLst*1.0/flows;
		    			finallengLst=avgLenLst/acceptNoLst;
		    			finalRunTime= runTime/flows;
			    	
		    			break;
		    		}
		    	}
		    }
			
			out.write("Alg_Subgradient "+infile+" "+ NumFlow+" "+ lamda +" "+ prob+" "+ finalblocking+" "+ finallengLst+ " " + maximumLinkLoad+ " "+finalRunTime+" ");
			if (algID ==1 || algID ==3 || algID==5)
				out.write(dem1*1.0/flows+" " +1.0*dem2/flows);			
			out.newLine();
		    }
			catch ( IOException e1 ) {
				e1.printStackTrace();
				} finally {
					if ( out != null )
						try {
							out.close();
							} catch (IOException e) {
								e.printStackTrace();}
					}    
			try {
		  		out.close();
		  		} catch (IOException e2) {
		  			e2.printStackTrace();
		  			}
		
	    
		return true;
	 
    
	}
	public static void main(String[] args)
	{
		//run with simulation (dinh dang moi ngay 04April 2018)


		//BufferedWriter out1 = null;
		
		
		int lamda=Integer.parseInt(args[0]); // = 5, 10, 15
		double processingTime = Double.parseDouble(args[1]);  // = 0.1 
		String fileName = args[2]; //= output.txt
		//int numFlow=Integer.parseInt(args[3]);
		double numFlow = Double.parseDouble(args[3]); // = 200
		String dirPath = args[4]; //newdata
		int algId=Integer.parseInt(args[5]); // = 1, 2, 3, 4
		double delPar = Double.parseDouble(args[6]);//=1 2 3
		int NoIdF=Integer.parseInt(args[7]); // = 5
		File dir = new File(dirPath);
		String[] extensions = new String[] { "txt" };
		@SuppressWarnings("unchecked")
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);

		
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					System.out.println("lambda: "+ lamda);
					ReadSmallData(file.getPath());
					fileName = file.getName();
					fileName = fileName.replace("input", "output");
					copyLinks = new ArrayList<>();
					funLoc = new ArrayList<>();
					//simulation_final(lamda,processingTime,fileName,numFlow,file.getPath(),algId,NoIdF);
					runSimulation(lamda,processingTime,fileName,numFlow,file.getPath(),algId,delPar,NoIdF);
//					for (int i=0;i<20;i++)
//					{
//						
//						exponentialRandom(0.2);// rate = 1/mean
//						poissonRandom(10.0);
//					}
					
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
	
	
		
		
	}
	public static void main1(String[] args) // Run 1 demands
	{
		
		ArrayList<Integer> sol=new ArrayList<>();
		int id_Demand = 0;
		File dir = new File(args[0]);
		String fileName;
		String[] extensions = new String[] { "txt" };
		int algID = Integer.parseInt(args[1]);
		int delPar = 1;
		@SuppressWarnings("unchecked")
		List<File> files = (List<File>) FileUtils.listFiles(dir, extensions, true);

		
			for (File file : files) {
				try {
					System.out.println("file: " + file.getCanonicalPath());
					ReadSmallData(file.getPath());
					fileName = file.getName();
					fileName = fileName.replace("input", "output");
					copyLinks = new ArrayList<>();
					sol= new ArrayList<>();
					funLoc = new ArrayList<>();
					ArrayList<Integer> arrFunc = new ArrayList<>();
					for(int i=0;i<functionArr.size();i++)
						arrFunc.add(functionArr.get(i).id());
			    	nDemand _d = new nDemand(++id_Demand, source, destination,default_b,arrFunc);
					
			    	switch (algID) {
					case 1:
						fileName= "MH1_"+fileName;
						sol = A_1(_d,g);
						break;
					case 2:
						fileName= "MH2_"+fileName;
						sol = A_2(_d,g);
						
						break;
					case 3:
						fileName= "SG1_"+fileName;
						sol = B_1(_d,g);
						break;
					case 4:
						fileName = "SG2_"+fileName;
						sol = B_2(_d,g,delPar);
						break;
//					case 5:
//						fileName = "GF_"+fileName;
//						sol = GreedyForward(_d,g);
//						break;
					default:
						break;
					}
					BufferedWriter out1;
			        try {  
			        	out1= new BufferedWriter(new FileWriter(fileName));
			        	
			        	for(int i=0;i<copyLinks.size();i++)
			        	{
			        		ArrayList<Pair> _t = copyLinks.get(i);
			        		out1.write((i+1)+": ");
			        		System.out.print((i+1)+" ");
			        		for(int j=0;j<_t.size();j++)
			        		{
			        			out1.write("("+_t.get(j).getnode()+","+_t.get(j).getfunction()+") ");
			        			System.out.print("("+_t.get(j).getnode()+","+_t.get(j).getfunction()+") ");
			        		}
			        		System.out.println();
			        		out1.newLine();
			        	}
			        	
			        	
			        	 out1.close();
					} catch (IOException e1) {
					e1.printStackTrace();
				}   	
		    
			
					
				} catch (IOException e) {
					e.printStackTrace();
				}
			}

	}
	
	public static void mainw(String[] args) // write small data for exact solution
	{
		int noVer = Integer.parseInt(args[0]);
		int NoFun = Integer.parseInt(args[1]);
		double p = Double.parseDouble(args[2]);
		int nodeCap = Integer.parseInt(args[3]);
		int linkCap = Integer.parseInt(args[4]);
		//int noNode = UtilizeFunction.randInt(noVer/3, noVer/2);
		int id=1;
		WriteSmallData(noVer, 10, p, "input100nodes.txt", 10, nodeCap, linkCap, 0.1);
		WriteSmallData(noVer+5, 5, p, "input150nodes.txt", 3, nodeCap, linkCap, 0.1);
		
//		for (int i=0;i<2;i++)
//		{
//			id+=i;
//			String fileName = "input"+ id+".txt";
//			WriteSmallData(noVer+i, NoFun, p, fileName, noNode, nodeCap, linkCap, 0.1);
//			
//		}

		
	}
	public static void mainOld(String[] args)
	{
		int noNode=40;
		int capa = 1;
		int noEd = Integer.parseInt(args[0]);
		int NoFun = Integer.parseInt(args[1]);
		double p = 0.037;
		WriteData(120,noEd, NoFun,p,"in4.txt",noNode,capa);
		WriteData(150,noEd, NoFun,p,"in5.txt",noNode,capa);
		WriteData(250,noEd, NoFun,p,"in6.txt",noNode,capa);
//		for (int i=0;i<3;i++)
//		{
//			noVer=100+i*100;
//			int j=i+1;
//			String fileName = "in"+ j+".txt";
//		
//			WriteData(noVer,noEd, NoFun,p,fileName);
//		}
		
	}
	public static void mainInp(String[] args)
	{
		int noVertex= 200;
		int noNode=30;
		double _cap = 0.75;
		double _w = 0.125;
		double _q = 0.1;
		double p = 0.032;
		
//		CreateInput(200, 10, 0.015, "input16.txt", 20, 3, 2, 0.1);
//		CreateInput(200, 10, 0.02, "input17.txt", 20, 3, 2, 0.1);
//		CreateInput(200, 10, 0.07, "input18.txt", 20, 3, 2, 0.1);
//		CreateInput(200, 10, 0.032, "in19.txt", 40, 4, 1.14, 0.1);
//		CreateInput(200, 10, 0.032, "in20.txt", 40, 1.71, 2.66, 0.1);
//		CreateInput(200, 10, 0.032, "in21.txt", 40, 1.71, 1.14, 0.1);
//		CreateInput(200, 10, 0.032, "in22.txt", 40, 4, 1.14, 0.1);
//		CreateInput(200, 10, 0.032, "in23.txt", 40, 1.71, 2.66, 0.1);
//		CreateInput(200, 10, 0.032, "in24.txt", 40, 1.71, 1.14, 0.1);
//		CreateInput(200, 10, 0.032, "in25.txt", 40, 4, 1.14, 0.1);
//		CreateInput(200, 10, 0.032, "in26.txt", 40, 1.71, 2.66, 0.1);
//		CreateInput(200, 10, 0.032, "in27.txt", 40, 1.71, 1.14, 0.1);
		
		CreateInput(200, 10, 0.027, "in1.txt", 5, 4, 1.14, 0.1);
		CreateInput(200, 10, 0.027, "in2.txt", 5, 1.71, 2.66, 0.1);
		CreateInput(200, 10, 0.027, "in3.txt", 5, 1.71, 1.14, 0.1);
		CreateInput(200, 10, 0.027, "in4.txt", 20, 4, 1.14, 0.1);
		CreateInput(200, 10, 0.027, "in5.txt", 20, 1.71, 2.66, 0.1);
		CreateInput(200, 10, 0.027, "in6.txt", 20, 1.71, 1.14, 0.1);
		CreateInput(200, 10, 0.027, "in7.txt", 40, 4, 1.14, 0.1);
		CreateInput(200, 10, 0.027, "in8.txt", 40, 1.71, 2.66, 0.1);
		CreateInput(200, 10, 0.027, "in9.txt", 40, 1.71, 1.14, 0.1);
		
	}
	
	public static void mainIIIIII(String[] args)
	{
		int noNode=20;
		int NoFun = 10;
		WriteDataFromFile(NoFun,"in1_brain.txt",noNode,"brain.txt",12.0,6.0,100.0,5.0);
		WriteDataFromFile(NoFun,"in2_brain.txt",noNode,"brain.txt",7.0,3.5,100.0,10.0);
		WriteDataFromFile(NoFun,"in3_brain.txt",noNode,"brain.txt",7.0,3.5,100.0,5.0);
		
	}

}