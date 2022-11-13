package in.ac.iisc.cds.dsl.cdgvendor.solver;

import java.util.ArrayList;
import java.util.List;

import org.json.JSONArray;

public class DFvector {

	private List<Long> d = new ArrayList<>();
	private List<Long> f = new ArrayList<>();
	
	public DFvector(JSONArray d, JSONArray f) {
		
		for(int i=0; i< d.length(); i++) {
			this.d.add(d.getLong(i));
			this.f.add(f.getLong(i));
		}
		
	}
	
	public DFvector(List<Long> d, List<Long> f) {
		
		
		// sorting on d  values
		for(int i=0; i < d.size(); i++) {
			for(int j=0; j < d.size()-i-1; j++) {
				
				if(d.get(j) < d.get(j+1)) {
					Long temp = d.get(j);
					d.set(j, d.get(j+1));
					d.set(j+1, temp);
					
					Long tempf = f.get(j);
					f.set(j, f.get(j+1));
					f.set(j+1, tempf);
					
				}
				
			}
		}
		
		for(int i=0; i< d.size(); i++) {
			this.d.add(d.get(i));
			this.f.add(f.get(i));
		}
	}
	
	public List<Long> getD(){
		return this.d;
	}
	
	public List<Long> getF(){
		return this.f;
	}

	public void remove(int index) {
		
		d.remove(index);
		f.remove(index);	
	
		
	}

	public void update(int index, Long newf) {
		
		f.set(index, newf);
		
	}

	public void setF(int index, Long newf) {
		// TODO Auto-generated method stub
		f.set(index, newf);
	}
	
	
	@Override
	 public String toString(){//overriding the toString() method  
		  return d + "\n" + f + "\n";  
	}

	public float findError(DFvector dfVector) {
		long tupleCount = 0L;
		List<Long> dfArray1 = new ArrayList<>();
		
		for(int i=0; i < this.d.size(); i++) {
			tupleCount += this.d.get(i) * this.f.get(i);
			for(Long j=0L; j < this.f.get(i); j++) {
				dfArray1.add(d.get(i));
			}
			
		}
		
		
		List<Long> dfArray2 = new ArrayList<>();
		
		for(int i=0; i < dfVector.d.size(); i++) {
			
			for(Long j=0L; j < dfVector.f.get(i); j++) {
				dfArray2.add(dfVector.d.get(i));
			}
			
		}
		
		
		if(dfArray1.size() < dfArray2.size() ) {
			
			int l1 = dfArray2.size();
			int l2 = dfArray1.size();
			int val = l1 - l2;
			long i=0L;
			for(; i < val; i++) {
				dfArray1.add(0L);
				
			}
			System.out.print("");
			
		}
		else if (dfArray1.size() > dfArray2.size()) {
			
			int l1 = dfArray1.size();
			int l2 = dfArray2.size();
			int val = l1 - l2;
			long i=0L;
			for(; i < val; i++) {
				dfArray2.add(0L);
				
			}
			System.out.print("");
		}
			
			
		long sumx = 0L;
		for(int i=0; i < dfArray1.size(); i++) {
			
			sumx += Math.abs(dfArray1.get(i) - dfArray2.get(i));
			
		}
		
		return (float) (sumx/ (2* tupleCount*1.0)) ;
		
		
		
	}

	public boolean isEmpty() {
		
		if(d.isEmpty())
			return true;
		return false;
	}

	public Integer size() {
		// TODO Auto-generated method stub
		return d.size();
	}

	public DFvector copy() {
		
		List<Long> dValues = new ArrayList<>();
		List<Long> fValues = new ArrayList<>();
		for(int i=0; i < this.d.size(); i++) {
			dValues.add(this.d.get(i));
			fValues.add(this.f.get(i));
		}
		
		return new DFvector(dValues, fValues);
	}

	public void removeDF(DFvector dFvector) {
		
		for(int i=0; i < dFvector.getD().size(); i++) {
			
			List<Long> dValues = dFvector.getD();
			List<Long> fValues = dFvector.getF();
			boolean flag = false;
			
				
				for(int di=0; di < this.getD().size(); di++ ) {
					if(dValues.get(i).longValue() == this.getD().get(di).longValue()) {
						
						if(fValues.get(i).longValue() == this.getF().get(di).longValue()) {
							this.remove(di);
							flag = true;
							break;
							
						}
						
						else if(fValues.get(i).longValue() < this.getF().get(di).longValue()) {
							flag = true;
							this.update(di, this.getF().get(di).longValue() - fValues.get(i).longValue());
							break;
						}
						
						else {
							
							throw new RuntimeException("More than required f assigned");
						}
						
						
					}
				}
				
				
				if(!flag) {
					throw new RuntimeException("d value not found");
				}
				
				
			
			
		}
		
	}  

	
}
