package chord.analyses.mln.dataraceabs;

import static chord.util.RelUtil.pRel;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chord.analyses.alias.Ctxt;
import chord.analyses.alias.DomC;
import chord.analyses.mln.ConstraintItem;
import chord.analyses.mln.MLNAnalysisDriver;
import chord.analyses.ursa.classifier.AllFalseClassifier;
import chord.analyses.ursa.classifier.BaggedClassifier;
import chord.analyses.ursa.classifier.Classifier;
import chord.analyses.ursa.classifier.datarace.DynamicAnalysisClassifier;
import chord.analyses.ursa.classifier.datarace.HandCraftedClassifier;
import chord.bddbddb.Dom;
import chord.project.Chord;
import chord.project.ClassicProject;
import chord.project.Config;
import chord.project.ITask;
import chord.project.analyses.ProgramRel;
import chord.project.analyses.provenance.Tuple;

import chord.analyses.alias.DomC;
import chord.analyses.alloc.DomH;
import chord.analyses.argret.DomK;
import chord.analyses.invk.DomI;
import chord.analyses.var.DomV;
import joeq.Compiler.Quad.Quad;
import java.util.Scanner;
import java.io.FileReader;
import java.io.File;
import java.io.PrintWriter;

import chord.analyses.mln.LookUpRule;
import java.util.Iterator;


/**
 * -Dchord.mln.nonpldiK
 * -Dchord.mln.pointer
 * -Dchord.ursa.classifier=<craftedAggr/craftedCons/dynamic/bag/uniform>
 * 
 * @author Ravi
 * @author Xin
 *
 */
@Chord(name = "dataraceAbs-mln-gen")
public class MLNDataraceAbsDriver extends MLNAnalysisDriver {
    private int nonPLDIK;
    private String pointerAnalysis;
    private boolean useThrEsc;
    private String thrEscFile;
    private String classifierKind;

    @Override
    protected Set<String> getDerivedRelations(){
        Set<String> ret = new HashSet<String>();

        //mhp-cs-dlog
        ret.add("threadAC");
        ret.add("threadACH");
        ret.add("threadPM_cs");
        ret.add("threadPH_cs");
        ret.add("simplePM_cs");
        ret.add("simplePH_cs");
        ret.add("simplePT_cs");
        ret.add("PathEdge_cs");
        ret.add("mhp_cs");
        ret.add("SummEdge_cs");
    
        //flowins-thresc-cs-dlog
        ret.add("escO");
        ret.add("CEC");

        //datarace-parallel-include-cs-dlog
        ret.add("mhe_cs");

        //datarace-cs-noneg-dlog
        ret.add("statE");
        ret.add("escapingRaceHext");
        ret.add("parallelRaceHext");
        ret.add("datarace");
        ret.add("racePairs_cs");

        return ret;
    }

    @Override
    protected Set<String> getDomains() {
        Set<String> ret = new HashSet<String>();

        //mhp-cs-dlog
        ret.add("AS");
        ret.add("I");
        ret.add("M");
        ret.add("P");
        ret.add("C");
    
        //flowins-thresc-cs-dlog
        ret.add("E");
        ret.add("M");
        ret.add("V");
        ret.add("Z");
        ret.add("C");
        ret.add("F");

        //datarace-parallel-include-cs-dlog
        ret.add("AS");
        ret.add("E");
        ret.add("P");
        ret.add("C");
        
        //datarace-cs-noneg-dlog
        ret.add("AS");
        ret.add("E");
        ret.add("K");
        ret.add("C");
        ret.add("F");

        return ret;
    }

    @Override
    protected Set<String> getInputRelations() {
        Set<String> ret = new HashSet<String>();

        //mhp-cs-dlog
        ret.add("PP");
        ret.add("MPhead");
        ret.add("MPtail");
        ret.add("PI");
        ret.add("CICM");
        ret.add("threadACM");
        ret.add("threadStartI");
        ret.add("threadCICM");
    
        //flowins-thresc-cs-dlog
        ret.add("CVC");
        ret.add("FC");
        ret.add("CFC");
        ret.add("MmethArg");
        ret.add("EV");
        ret.add("escE");
        
        //datarace-parallel-include-cs-dlog
        ret.add("PE");
    //  ret.add("mhp_cs");

        //datarace-cs-noneg-dlog
        ret.add("EF");
        ret.add("statF");
        ret.add("excludeSameThread");
        ret.add("unlockedRaceHext");
    //  ret.add("mhe_cs");
    //  ret.add("CEC");

        return ret;
    }

    @Override
    protected String getQueryRelation(){
        return "racePairs_cs";
    }

    @Override
    protected String[] getConfigFiles() {
        String[] configFiles = new String[4];
        String chordMain = System.getenv("CHORD_INCUBATOR"); 
        configFiles[0] = chordMain + File.separator + "src/chord/analyses/mln/datarace/flowins-thresc-cs-dlog_XZ89_.config";
        configFiles[1] = chordMain + File.separator + "src/chord/analyses/mln/datarace/mhp-cs-dlog_XZ89_.config";
    //  configFiles[1] = chordMain + File.separator + "src/chord/analyses/mln/datarace/datarace-escaping-include-cs-dlog_XZ89_.config";
        configFiles[2] = chordMain + File.separator + "src/chord/analyses/mln/datarace/datarace-parallel-include-cs-dlog_XZ89_.config";
        if (this.runningBase) {
            configFiles[3] = chordMain + File.separator + "src/chord/analyses/mln/dataraceabs/datarace-cs-noneg-abs-dlog_XZ89_.config";
            // configFiles[3] = chordMain + File.separator + "src/chord/analyses/mln/datarace/datarace-cs-noneg-dlog_XZ89_.config";
        }
        return configFiles;
    }

    @Override
    protected void genTasks(){
        tasks = new ArrayList<ITask>();
        tasks.add(ClassicProject.g().getTask("cipa-0cfa-dlog"));
        // tasks.add(ClassicProject.g().getTask("HIDumper-java"));
        tasks.add(ClassicProject.g().getTask("simple-pro-ctxts-java-abs"));
        tasks.add(ClassicProject.g().getTask("pro-argCopy-dlog"));
        tasks.add(ClassicProject.g().getTask("kobj-abs-init-dlog_XZ89_"));
        tasks.add(ClassicProject.g().getTask("pro-cspa-kobj-dlog_XZ90_"));
        tasks.add(ClassicProject.g().getTask("thrSenCSCG-dlog"));
        tasks.add(ClassicProject.g().getTask("reachableACM-dlog"));
        tasks.add(ClassicProject.g().getTask("syncCLC-dlog"));
        if (Boolean.getBoolean("chord.datarace.exclude.nongrded"))
            tasks.add(ClassicProject.g().getTask("datarace-nongrded-exclude-cs-dlog"));
        else
            tasks.add(ClassicProject.g().getTask("datarace-nongrded-include-cs-dlog"));
        if (Boolean.getBoolean("chord.mln.dataraceabs.bingo")){
            tasks.add(ClassicProject.g().getTask("escE-java")); //PLDI'16
        }else{
            tasks.add(ClassicProject.g().getTask("queryE-abs"));
            tasks.add(ClassicProject.g().getTask("flowins-thresc-dlog"));
        }
        tasks.add(ClassicProject.g().getTask("datarace-cs-init-dlog"));
    //  tasks.add(ClassicProject.g().getTask("mhp-cs-dlog"));
        
        // we use the instrumented files from as we need all derivation paths for reverted constraints
        // also, we need to output all relations
        tasks.add(ClassicProject.g().getTask("flowins-thresc-cs-dlog_XZ89_"));
        tasks.add(ClassicProject.g().getTask("mhp-cs-dlog_XZ89_"));
        tasks.add(ClassicProject.g().getTask("datarace-parallel-include-cs-dlog_XZ89_"));
    //  tasks.add(ClassicProject.g().getTask("datarace-escaping-include-cs-dlog_XZ89_"));
        if (this.runningBase) {
            tasks.add(ClassicProject.g().getTask("datarace-cs-noneg-abs-dlog_XZ89_"));
            // tasks.add(ClassicProject.g().getTask("datarace-cs-noneg-dlog_XZ89_"));
        } else {
            tasks.add(ClassicProject.g().getTask("datarace-cs-noneg-abs-dlog"));
        }
    }

    ProgramRel IKRel;
    ProgramRel HKRel;
    ProgramRel OKRel;
    DomI domI;
    DomH domH;
    DomV domV;
    DomK domK;

    /**
     * Invoke kobj-refiner to get the result.
     */
    @Override
    protected void runOracle(){
        try{
            String prefix = Config.outDirName + File.separator;
            PrintWriter printWriter = new PrintWriter(new File(prefix + "domH.txt"));
            int numH = domH.size();
            for(int i = 1;i < numH;i++){
                Quad quad = (Quad) domH.get(i);
                printWriter.println(i + ":" + quad.getMethod() + "\t" + quad.toString());
            }
            printWriter.close();
            printWriter = new PrintWriter(new File(prefix + "numH.txt"));
            printWriter.println(numH - 1);
            printWriter.close();
        }catch(Exception e){
            e.printStackTrace();
        }
        System.setProperty("chord.ctxt.kind", "co");
        HKRel.zero();
        for (int i = 1; i < domH.size(); i++) {
            Quad H = (Quad) domH.get(i);
            HKRel.add(H, 3);
        }
        HKRel.save();

        OKRel.zero();
        for(int i = 1; i < domH.size(); i++){
            Quad H = (Quad) domH.get(i);
            OKRel.add(H, 3);
        }
        OKRel.save();
        if (this.useThrEsc)
            System.setProperty("chord.mln.threscFile", this.thrEscFile);
        areCurrentRelsOracle = true;

        for (ITask t : tasks) {
            ClassicProject.g().resetTaskDone(t);
            ClassicProject.g().runTask(t);
        }
    }
    /**
     * Run 0-cfa
     */
	@Override
	protected void runBaseCase(){
		IKRel = (ProgramRel) ClassicProject.g().getTrgt("IK");
		HKRel = (ProgramRel) ClassicProject.g().getTrgt("HK");
		OKRel = (ProgramRel) ClassicProject.g().getTrgt("OK");
		domI = (DomI) ClassicProject.g().getTrgt("I");
		domK = (DomK) ClassicProject.g().getTrgt("K");
		domH = (DomH) ClassicProject.g().getTrgt("H");
		ClassicProject.g().runTask(domI);
		ClassicProject.g().runTask(domK);
		ClassicProject.g().runTask(domH);
		ClassicProject.g().runTask(ClassicProject.g().getTask("E"));
		IKRel.zero();
		for (int i = 0; i < domI.size(); i++) {
			Quad I = (Quad) domI.get(i);
			IKRel.add(I, 0);
		}
		IKRel.save();
		System.setProperty("chord.ctxt.kind", "co");
		if (this.mode == Mode.ORACLE)
		System.clearProperty("chord.mln.threscFile");
		HKRel.zero();
		OKRel.zero();
		try {
			if (System.getProperty("chord.mln.dataraceabs") == null) {
				for (int i = 1; i < domH.size(); i++) {
					Quad H = (Quad) domH.get(i);
					HKRel.add(H, 3);
					OKRel.add(H, 3);
				}
			} else {
				Scanner scanner = new Scanner(new FileReader(System.getProperty("chord.mln.dataraceabs")));
				for (int i = 1; i < domH.size(); i++) {
					int level = scanner.nextInt();
					Quad H = (Quad) domH.get(i);
					HKRel.add(H, level == 0 ? 1 : level);
					OKRel.add(H, level);
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
		HKRel.save();
		OKRel.save();
		for (ITask t : tasks) {
			ClassicProject.g().resetTaskDone(t);
			ClassicProject.g().runTask(t);
		}
				java.util.Map<joeq.Compiler.Quad.Quad, String> quadDescCache = new java.util.HashMap<joeq.Compiler.Quad.Quad, String>();
		java.util.Map<joeq.Class.jq_Method, String> methodDescCache = new java.util.HashMap<joeq.Class.jq_Method, String>();
		java.util.Map<joeq.Class.jq_Field, String> fieldDescCache = new java.util.HashMap<joeq.Class.jq_Field, String>();
		class Formatter {
			String safeFileName(String name) {
				return name == null ? "" : name;
			}
			String buildMethodDescription(joeq.Class.jq_Method method) {
				if (method == null)
					return "unknown method";
				String cached = methodDescCache.get(method);
				if (cached != null)
					return cached;
				StringBuilder sb = new StringBuilder();
				joeq.Class.jq_Class cls = method.getDeclaringClass();
				String clsName = cls == null ? "unknown" : cls.getName();
				sb.append(clsName);
				sb.append('.');
				sb.append(method.getName());
				sb.append(method.getDesc());
				sb.append(" defined at " );
				String fileName = cls == null ? "" : cls.getSourceFileName();
				sb.append(safeFileName(fileName));
				sb.append(':');
				sb.append(method.getLineNumber(0));
				String desc = sb.toString();
				methodDescCache.put(method, desc);
				return desc;
			}
			String quadLocation(joeq.Compiler.Quad.Quad quad) {
				if (quad == null)
					return "unknown quad";
				String cached = quadDescCache.get(quad);
				if (cached != null)
					return cached;
				joeq.Class.jq_Method method = quad.getMethod();
				String methodInfo = buildMethodDescription(method);
				joeq.Class.jq_Class cls = method.getDeclaringClass();
				String fileName = cls == null ? "" : cls.getSourceFileName();
				String result = methodInfo + " @ " + safeFileName(fileName) + ":" + quad.getLineNumber() + " :: " + quad.toString();
				quadDescCache.put(quad, result);
				return result;
			}
			String instLocation(Object inst) {
				if (inst == null)
					return "null program point";
				if (inst instanceof joeq.Compiler.Quad.Quad)
					return "quad " + quadLocation((joeq.Compiler.Quad.Quad) inst);
				joeq.Compiler.Quad.BasicBlock bb = (joeq.Compiler.Quad.BasicBlock) inst;
				joeq.Class.jq_Method method = bb.getMethod();
				String methodInfo = buildMethodDescription(method);
				return "basic block " + bb.getID() + " of " + methodInfo;
			}
			String contextDescription(chord.analyses.alias.Ctxt ctxt) {
				if (ctxt == null)
					return "epsilon context";
				joeq.Compiler.Quad.Quad[] elems = ctxt.getElems();
				if (elems.length == 0)
					return "epsilon context";
				StringBuilder sb = new StringBuilder();
				sb.append("context [");
				for (int i = 0; i < elems.length; i++) {
					if (i > 0)
						sb.append("; ");
					sb.append(quadLocation(elems[i]));
				}
				sb.append(']');
				return sb.toString();
			}
			String variableDescription(DomV domVLocal, joeq.Compiler.Quad.RegisterFactory.Register reg) {
				if (reg == null)
					return "null variable";
				joeq.Class.jq_Method owner = domVLocal.getMethod(reg);
				String ownerDesc = buildMethodDescription(owner);
				String varName = owner == null ? "unknown" : owner.getRegName(reg);
				return "variable " + varName + " in " + ownerDesc;
			}
			String fieldDescription(joeq.Class.jq_Field field) {
				if (field == null)
					return "array element synthetic field";
				String cached = fieldDescCache.get(field);
				if (cached != null)
					return cached;
				joeq.Class.jq_Class cls = field.getDeclaringClass();
				String fileName = cls == null ? "" : cls.getSourceFileName();
				String desc = cls.getName() + "." + field.getName() + " defined at " + safeFileName(fileName) + ":0";
				fieldDescCache.put(field, desc);
				return desc;
			}
			String threadDescription(chord.util.tuple.object.Pair<?, ?> pair) {
				if (pair == null)
					return "no abstract thread (placeholder)";
				joeq.Compiler.Quad.Quad start = (joeq.Compiler.Quad.Quad) pair.val0;
				joeq.Class.jq_Method rootMethod = (joeq.Class.jq_Method) pair.val1;
				return "thread started at " + quadLocation(start) + " with root method " + buildMethodDescription(rootMethod);
			}
		}
		Formatter formatter = new Formatter();
		java.util.List<String> orderedDomains = new java.util.ArrayList<String>();
		orderedDomains.add("AS");
		orderedDomains.add("I");
		orderedDomains.add("M");
		orderedDomains.add("P");
		orderedDomains.add("C");
		orderedDomains.add("E");
		orderedDomains.add("V");
		orderedDomains.add("Z");
		orderedDomains.add("F");
		orderedDomains.add("K");
		java.util.LinkedHashMap<String, ProgramDom<?>> domainMap = new java.util.LinkedHashMap<String, ProgramDom<?>>();
		ClassicProject project = ClassicProject.g();
		for (String domName : orderedDomains) {
			try {
				ProgramDom<?> dom = (ProgramDom<?>) project.getTrgt(domName);
				if (dom != null) {
					project.runTask(dom);
					domainMap.put(domName, dom);
				}
			} catch (Throwable ignored) { }
		}
		java.io.File outDir = new java.io.File(Config.outDirName + File.separator);
		if (!outDir.exists())
			outDir.mkdirs();
		java.io.File combinedFile = new java.io.File(outDir, "dom_info.tsv");
		java.io.PrintWriter combinedWriter = null;
		try {
			combinedWriter = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(combinedFile)));
			for (java.util.Map.Entry<String, ProgramDom<?>> entry : domainMap.entrySet()) {
				String domName = entry.getKey();
				ProgramDom<?> dom = entry.getValue();
				java.io.File domFile = new java.io.File(outDir, "dom_" + domName + ".txt");
				java.io.PrintWriter domWriter = new java.io.PrintWriter(new java.io.BufferedWriter(new java.io.FileWriter(domFile)));
				domWriter.println("# Domain " + domName + " entries");
				for (int idx = 0; idx < dom.size(); idx++) {
					Object val = dom.get(idx);
					String desc;
					if ("AS".equals(domName)) {
						desc = formatter.threadDescription((chord.util.tuple.object.Pair<?, ?>) val);
					} else if ("I".equals(domName) || "E".equals(domName)) {
						desc = formatter.quadLocation((joeq.Compiler.Quad.Quad) val);
					} else if ("M".equals(domName)) {
						desc = formatter.buildMethodDescription((joeq.Class.jq_Method) val);
					} else if ("P".equals(domName)) {
						desc = formatter.instLocation(val);
					} else if ("C".equals(domName)) {
						desc = formatter.contextDescription((chord.analyses.alias.Ctxt) val);
					} else if ("V".equals(domName)) {
						desc = formatter.variableDescription((DomV) dom, (joeq.Compiler.Quad.RegisterFactory.Register) val);
					} else if ("Z".equals(domName)) {
						Integer pos = (Integer) val;
						desc = pos == null ? "unknown argument position" : "argument position " + pos.intValue();
					} else if ("F".equals(domName)) {
						desc = formatter.fieldDescription((joeq.Class.jq_Field) val);
					} else if ("K".equals(domName)) {
						Integer cfg = (Integer) val;
						desc = cfg == null ? "configuration value" : "configuration value " + cfg.intValue();
					} else {
						desc = val == null ? "" : val.toString();
					}
					String line = idx + "\t" + desc;
					domWriter.println(line);
					combinedWriter.println(domName + "\t" + idx + "\t" + desc);
				}
				domWriter.flush();
				domWriter.close();
			}
		} catch (Exception e) {
			throw new RuntimeException(e);
		} finally {
			if (combinedWriter != null) {
				combinedWriter.flush();
				combinedWriter.close();
			}
		}

		areCurrentRelsOracle = false;
		if(this.mode == Mode.ORACLE) return;
		try {
			try {
				PrintWriter constraintFile = new PrintWriter(new BufferedWriter(new FileWriter(Config.outDirName + File.separator + "kobj_named_cons_all.txt")));
				if(!System.getProperty("chord.mln.dataraceabs.outputkobj", "true").equals("false")){
					List<LookUpRule> rules = new ArrayList<LookUpRule>();
					String[] configFiles = new String[2];
					String chordMain = System.getenv("CHORD_INCUBATOR");
					configFiles[0] = chordMain + File.separator + "src/chord/analyses/mln/dataraceabs/kobj-abs-init-dlog_XZ89_.config";
					configFiles[1] = chordMain + File.separator + "src/chord/analyses/mln/kobj/pro-cspa-kobj-dlog_XZ90_.config";
					for (String conFile : configFiles) {
						Scanner sc = new Scanner(new File(conFile));
						while (sc.hasNext()) {
							String line = sc.nextLine().trim();
							if (!line.equals("")) {
								LookUpRule rule = new LookUpRule(line);
								rules.add(rule);
							}
						}
						sc.close();
					}
					for (int i = 0; i < rules.size(); i++) {
						LookUpRule rule = rules.get(i);
						String name = "R" + Integer.toString(i + 100);
						Iterator<ConstraintItem> iter = rule.getAllConstrIterator();
						while (iter.hasNext()) {
							this.printNamedConstraint(constraintFile, name, iter.next());
						}
					}
				}
				constraintFile.flush();
				constraintFile.close();

				// PrintWriter printWriter = new PrintWriter(new File(Config.outDirName + File.separator + "CICM.txt"));
				// ProgramRel cicm = (ProgramRel) ClassicProject.g().getTrgt("CICM");
				// cicm.load();
				// Set<List<Integer>> st = new HashSet();
				// for (int[] vals : cicm.getAryNIntTuples()) {
					// List<Integer> list = new ArrayList();
					// list.add(vals[1]);
					// list.add(vals[3]);
					// st.add(list);
					// }
					// for(List<Integer> list : st){
						// printWriter.println(list.get(0) + " " + list.get(1));
						// }
						// for(int i = 0;i < domI.size();i++){
							// printWriter.println(domI.get(i));
							// }
							// printWriter.flush();
							// printWriter.close();
						} catch (Exception e) {
							throw new RuntimeException(e);
						}
						// try{
							// String prefix = Config.outDirName + File.separator;
							// PrintWriter printWriter = new PrintWriter(new File(prefix + "CICM.txt"));
							// ProgramRel CICMRel = (ProgramRel) ClassicProject.g().getTrgt("racePairs_cs");
							// ProgramRel denyHRel = (ProgramRel) ClassicProject.g().getTrgt("DenyH");
							// ProgramRel denyORel = (ProgramRel) ClassicProject.g().getTrgt("DenyO");
							// CICMRel.load();
							// for (int[] vals : CICMRel.getAryNIntTuples()) {
								// Tuple tuple = new Tuple(CICMRel, vals);
								// Set<Tuple> tuples = getProvenance(tuple);
								// Set<Integer> Hs = new HashSet();
								// for(Tuple tuple1 : tuples){
									// printWriter.println(tuple1);
									// ProgramRel rel = tuple1.getRel();
									// if(rel.equals(denyHRel) || rel.equals(denyORel)){
										// Hs.add(tuple1.getIndices()[0]);
										// }
										// }
										// for(int i : vals) printWriter.print(i + " ");
										// printWriter.println();
										// for(Integer i : Hs) printWriter.print(i + " ");
										// printWriter.println();
										// }
										// printWriter.close();
										// }catch(Exception e){
											// e.printStackTrace();
											// }
										}
    //In kobj, there're two kinds of Cs: H and O. For simplicity, we project t to both possibilities
    @Override
    protected Set<Tuple> project(Tuple t){
        int[] newIndicies = new int[t.getIndices().length];
        Set<Tuple> ret = this.projectRecursively(t, newIndicies, 0);
        return ret;
    }

    private Set<Tuple> projectRecursively(Tuple t, int[] newIndicies, int index){
        Set<Tuple> ret = new HashSet<Tuple>();
        Dom doms[] = t.getDomains();
        Dom d = doms[index];
        int oriIndicies[] = t.getIndices();
        if(d instanceof DomC){
            DomC dc = (DomC)d;
            Ctxt ct = dc.get(oriIndicies[index]);
            Ctxt ct1 = ct.prefix(0);
            Ctxt ct2 = ct.prefix(1);
            int[] newIndicies1 = new int[newIndicies.length];
            int[] newIndicies2 = new int[newIndicies.length];
            System.arraycopy(newIndicies, 0, newIndicies1, 0, newIndicies.length);
            System.arraycopy(newIndicies, 0, newIndicies2, 0, newIndicies.length);
            newIndicies1[index] = dc.indexOf(ct1);
            newIndicies2[index] = dc.indexOf(ct2);
            if(index == newIndicies.length-1){
                Tuple t1 = new Tuple(t.getRel(),newIndicies1);
                Tuple t2 = new Tuple(t.getRel(),newIndicies2);
                ret.add(t1);
                ret.add(t2);
            }else{
                index++;
                ret.addAll(this.projectRecursively(t, newIndicies1, index));
                ret.addAll(this.projectRecursively(t, newIndicies2, index));
            }
        }else{
            int[] newIndicies1 = new int[newIndicies.length];
            System.arraycopy(newIndicies, 0, newIndicies1, 0, newIndicies.length);
            newIndicies1[index] = oriIndicies[index];
            if(index == newIndicies.length-1){
                Tuple t1 = new Tuple(t.getRel(),newIndicies1);
                ret.add(t1);
            }else{
                index++;
                ret.addAll(this.projectRecursively(t, newIndicies1, index));
            }        
        }
        return ret;
    }

    @Override
    protected void readSettings(){
        super.readSettings();
        this.nonPLDIK = Integer.getInteger("chord.mln.nonpldiK", 1);
        this.useThrEsc = Boolean.getBoolean("chord.mln.useThrEsc");
        this.thrEscFile = System.getProperty("chord.mln.threscFile");
        this.classifierKind = System.getProperty("chord.ursa.classifier", "dynamic");
        if (this.useThrEsc && this.thrEscFile == null) {
            throw new RuntimeException("Specify thread escape proven queries file.");
        }
        
        this.pointerAnalysis = System.getProperty("chord.mln.pointer", "kcfa");
        if(!this.pointerAnalysis.equals("kcfa") && !this.pointerAnalysis.equals("kobj")){
            throw new RuntimeException("Unknown pointer analysis");
        } 

        // for ursa:
//      System.setProperty("chord.datarace.exclude.init", "false");
//      System.setProperty("chord.datarace.exclude.eqth", "true");
//      System.setProperty("chord.datarace.exclude.nongrded", "true");
        // for fse15:
//      System.setProperty("chord.datarace.exclude.init", "true");
//      System.setProperty("chord.datarace.exclude.eqth", "true");
//      System.setProperty("chord.datarace.exclude.nongrded", "false");
    }

    @Override
    protected List<Tuple> getAxiomTuples() {
        List<Tuple> axiomTuples = new ArrayList<Tuple>();
        axiomTuples.add(new Tuple(pRel("PathEdge_cs"), new int[]{0, 0, 1, 0, 0}));
        return axiomTuples;
    }

    @Override
    public void run() {
        super.run();
        // ClassicProject.g().runTask("orderedEE-dlog");
        // ProgramRel orderedEE = (ProgramRel)ClassicProject.g().getTrgt("OrderedEE");
        // orderedEE.load();
        // try {
        //  PrintWriter pw = new PrintWriter(new File(Config.outDirName+File.separator+"correlEE.txt"));
        //  for(int n[] : orderedEE.getAryNIntTuples()){
        //      for(int i : n)
        //          pw.print("escE("+i+") ");
        //      pw.println();
        //  }
        //  pw.flush();
        //  pw.close();
        // } catch (FileNotFoundException e) {
        //  throw new RuntimeException(e);
        // }    
    }

    @Override
    protected void predict(Set<Tuple> tuples, Set<ConstraintItem> provenance, String classifierPath) {
        try {
            PrintWriter pw = new PrintWriter(new File(Config.outDirName + File.separator + "prediction.txt"));
            Classifier classifier = null;
            if(this.classifierKind.equals("dynamic")){
                classifier = new DynamicAnalysisClassifier();
            }
            else if (this.classifierKind.equals("craftedAggr"))
                classifier = new HandCraftedClassifier(true);
            else if (this.classifierKind.equals("craftedCons"))
                classifier = new HandCraftedClassifier(false);
            else if (this.classifierKind.equals("bag"))
                classifier = new BaggedClassifier();
            else if (this.classifierKind.equals("uniform"))
                classifier = new AllFalseClassifier();
            else
                throw new RuntimeException("Unknown classifier "+this.classifierKind);
            for (Tuple t : tuples) {
                pw.println(t+" "+classifier.predictFalse(t, provenance));
            }
            pw.flush();
            pw.close();
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            System.exit(1);
        }

    }

    @Override
    protected void generateAppScope(String fileName) {
        // ClassicProject.g().runTask("checkExcludedP-dlog");
        // ClassicProject.g().runTask("checkExcludedI-dlog");
        // ClassicProject.g().runTask("checkExcludedE-dlog");
        
        // ProgramRel checkExcludedI = (ProgramRel)ClassicProject.g().getTrgt("checkExcludedI");
        // checkExcludedI.load();
        // ProgramRel checkExcludedP = (ProgramRel)ClassicProject.g().getTrgt("checkExcludedP");
        // checkExcludedP.load();
        // ProgramRel checkExcludedE = (ProgramRel)ClassicProject.g().getTrgt("checkExcludedE");
        // checkExcludedE.load();
        
        // try {
        //  PrintWriter pw = new PrintWriter(new File(fileName));

        //  // app causes
        //  ProgramRel pathEdge = (ProgramRel) ClassicProject.g().getTrgt("PathEdge_cs");
        //  pathEdge.load();
            
        //  for(int content[] : pathEdge.getAryNIntTuples()){
        //      Tuple t = new Tuple(pathEdge,content);
        //      // check if P is app P
        //      if(!checkExcludedP.contains(content[1]))
        //          pw.println(t.toString());
        //  }
            
        //  ProgramRel escE = (ProgramRel) ClassicProject.g().getTrgt("escE");
        //  escE.load();
            
        //  for(int content[] : escE.getAryNIntTuples()){
        //      Tuple t = new Tuple(escE,content);
        //      // check if E is appE
        //      if(!checkExcludedE.contains(content[0]))
        //          pw.println(t.toString());
        //  }
            
        //  ProgramRel cicm = (ProgramRel) ClassicProject.g().getTrgt("CICM");
        //  cicm.load();
            
        //  for(int content[] : cicm.getAryNIntTuples()){
        //      Tuple t = new Tuple(cicm,content);
        //      //check if I is appI
        //      if(!checkExcludedI.contains(content[1]))
        //          pw.println(t.toString());
        //  }
            
        //  ProgramRel race = (ProgramRel) ClassicProject.g().getTrgt("racePairs_cs");
        //  race.load();
            
        //  for(int content[] : race.getAryNIntTuples()){
        //      Tuple t = new Tuple(race,content);
        //      pw.println(t.toString());
        //  }
            
        //  pw.flush();
        //  pw.close();

        // } catch (FileNotFoundException e) {
        //  e.printStackTrace();
        //  System.exit(1);
        // }
    }    
    
}
