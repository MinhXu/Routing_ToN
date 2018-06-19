

import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Random;
import java.util.Vector;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;

public class UtilizeFunction {
	/**
	 * Returns a psuedo-random number between min and max, inclusive.
	 * The difference between min and max can be at most
	 * <code>Integer.MAX_VALUE - 1</code>.
	 *
	 * @param min Minimim value
	 * @param max Maximim value.  Must be greater than min.
	 * @return Integer between min and max, inclusive.
	 * @see java.util.Random#nextInt(int)
	 */
	
	public static boolean isPositive(Vector<Double> k)
	{
		for (int i=0;i<k.size();i++)
			if(k.get(i)<=0)
				return false;
		return true;
	}
	public static Vector<Double> add(Vector<Double> a, Vector<Double> b)
	{
		Vector<Double> temp = new Vector<Double>();
		if(a.size()!=b.size()) return null;
		for (int i=0;i<a.size();i++)
			temp.addElement(a.get(i)+b.get(i));
		return temp;
	}
	public static Vector<Double> minus(Vector<Double> a, Vector<Double> b)
	{
		Vector<Double> temp = new Vector<Double>();
		if(a.size()!=b.size()) return null;
		for (int i=0;i<a.size();i++)
			temp.addElement(a.get(i)-b.get(i));
		return temp;
	}
	public static double multi(Vector<Double> a, Vector<Double> b)
	{
		double temp=0.0;
		if(a.size()!=b.size()) return -1;
		for (int i=0;i<a.size();i++)
			
			temp+=a.get(i)*b.get(i);
		return temp;
	}
	public static int divide(Vector<Double> a, Vector<Double> b)
	{
		int temp_Min=Integer.MAX_VALUE;
		Vector<Integer> temp = new Vector<>(3);
		for (int i=0;i<3;i++)
		{
			Double  _t = a.get(i)/b.get(i);
			temp.addElement(_t.intValue());
		}
		for (int i=0;i<3;i++)
		{
			if(temp.get(i)<temp_Min)
				temp_Min= temp.get(i);
		}
		return temp_Min;
	}
	public static Vector<Double> multi(Vector<Double> a, double b)
	{
		Vector<Double> temp = new Vector<Double>();
		for (int i=0;i<a.size();i++)
			
			temp.addElement(b*a.get(i));
		return temp;
	}
	public static boolean isBig(Vector<Double> k1, Vector<Double> k2)
	{
		if(k1.get(0)>=k2.get(0)&& k1.get(1)>=k2.get(1)&& k1.get(2)>=k2.get(2))
			return true;
		else
			return false;
	}
	public static double value(Vector<Double> k)
	{
		double tam=0.0;
		for(int i=0;i<k.size();i++)
			tam+=k.get(i)*k.get(i);
		return Math.sqrt(tam);
	}
	public static int bigger(Vector<Double> k1, Vector<Double> k2)
	{
		// 1: k1 > k2
		// 2: k2 > k1
		// 0: k1 = k2
		//-1: k1 != k2
		if(k1.size() != k2.size()) return -1;
		if(k1.get(0)==k2.get(0))
			if(k1.get(1)==k2.get(1))
				if(k1.get(2)==k2.get(2))
					return 0;
				else
					if(k1.get(2)>k2.get(2))
						return 1;
					else
						return 2;
			else
				if(k1.get(1)>k2.get(1))
					return 1;
				else
					return 2;
		else
			if(k1.get(0)>k2.get(0))
				return 1;
			else
				return 2;
	}
	
	public static int randInt(int min, int max) {

	    // Usually this can be a field rather than a method variable
	    Random rand = new Random();

	    // nextInt is normally exclusive of the top value,
	    // so add 1 to make it inclusive
	    int randomNum = rand.nextInt((max - min) + 1) + min;

	    return randomNum;
	}
	
	
	public static double randDouble(double min, double max) {
	    double random = new Random().nextDouble();
		double result = min + (random * (max - min));

	    return result;
	}
	public static double randDouble(double min) {
		double max = 100.0;
	    double random = new Random().nextDouble();
		double result = min + (random * (max - min));
	    return result;
	}
	public static double randDouble(int hso) {

	    // Usually this can be a field rather than a method variable
	    Random rand = new Random();

	    // nextInt is normally exclusive of the top value,
	    // so add 1 to make it inclusive
	    double randomNum = rand.nextDouble()*hso;

	    return randomNum;
	}

	
	public static double randomDouble(Integer[] intArray)
	{
		//Integer[] intArray = new Integer[] { 100,150,200,400, 500 };
		
		ArrayList<Integer> asList = new ArrayList<Integer>(Arrays.asList(intArray));
		Collections.shuffle(asList);
		return Double.parseDouble(asList.get(0).toString());
	}
	public static void main()
	{
		//randomData("inputFile.txt");
		//randomData_lib("out.txt", 3, 5);
	}
}