package chord.analyses.ursa.cipa;

import static chord.util.RelUtil.pRel;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import chord.analyses.alias.Ctxt;
import chord.analyses.alloc.DomH;
import chord.analyses.field.DomF;
import chord.analyses.ursa.ConstraintItem;
import chord.analyses.ursa.URSAAnalysisDriver;
import chord.analyses.ursa.classifier.Classifier;
import chord.analyses.ursa.classifier.cipa.DynamicAnalysisClassifier;
import chord.bddbddb.Dom;
import chord.project.Chord;
import chord.project.ClassicProject;
import chord.project.Config;
import chord.project.ITask;
import chord.project.analyses.ProgramRel;
import chord.project.analyses.provenance.Tuple;
import chord.util.ArraySet;
import joeq.Class.jq_Field;
import joeq.Class.jq_Method;
import joeq.Compiler.Quad.Operator.Invoke;
import joeq.Compiler.Quad.Operator.New;
import joeq.Compiler.Quad.Quad;

/**
 * -Dchord.ursa.classifier=<dynamic/none>
 * 
 */
@Chord(name = "cipa-mln-gen", consumes = { "checkExcludedV", "checkExcludedH", "checkExcludedT", "checkExcludedI" })
public class URSAcipaDriver extends URSAAnalysisDriver {
	private static Set<String> relsWithLabels;
	private static Set<String> oracleRels;
	private String classifierKind;
	private Classifier classifier;

	static {
		relsWithLabels = new ArraySet<String>();
		relsWithLabels.add("VH");
		relsWithLabels.add("FH");
		relsWithLabels.add("HFH");
		relsWithLabels.add("reachableI");
		relsWithLabels.add("reachableM");
		relsWithLabels.add("IM");
		relsWithLabels.add("MM");

		relsWithLabels.add("ptsVH");

		oracleRels = new ArraySet<String>();
		oracleRels.add("CVC");
		oracleRels.add("FC");
		oracleRels.add("CFC");
		oracleRels.add("reachableCI");
		oracleRels.add("reachableCM");
		oracleRels.add("CICM");
		oracleRels.add("CMCM");
		oracleRels.add("ptsVH");
	}

	@Override
	protected Set<String> getDerivedRelations() {
		Set<String> ret = new HashSet<String>();

		// cipa-0cfa-dlog
		ret.add("IHM");
		ret.add("VV");
		ret.add("specIMV");
		ret.add("objValAsgnInst");
		ret.add("objVarAsgnInst");
		ret.add("getInstFldInst");
		ret.add("putInstFldInst");
		ret.add("getStatFldInst");
		ret.add("putStatFldInst");
		ret.add("reachableT");
		// ret.add("VHfilter"); move to input due to the wild card rule
		ret.add("VH");
		ret.add("FH");
		ret.add("HFH");
		ret.add("rootM");
		ret.add("reachableI");
		ret.add("reachableM");
		ret.add("IM");
		ret.add("MM");
		ret.add("reachableH");
		ret.add("reachableV");
		ret.add("ptsVH");

		return ret;
	}

	@Override
	protected Set<String> getDomains() {
		Set<String> ret = new HashSet<String>();

		// domains from cipa-0cfa-dlog
		ret.add("T");
		ret.add("F");
		ret.add("M");
		ret.add("I");
		ret.add("H");
		ret.add("V");
		ret.add("Z");

		return ret;
	}

	@Override
	protected Set<String> getInputRelations() {
		Set<String> ret = new HashSet<String>();

		// input relations from cipa-0cfa-dlog
		ret.add("VT");
		ret.add("HT");
		ret.add("cha");
		ret.add("sub");
		ret.add("MmethArg");
		ret.add("MmethRet");
		ret.add("IinvkArg0");
		ret.add("IinvkArg");
		ret.add("IinvkRet");
		ret.add("MI");
		ret.add("statIM");
		ret.add("specIM");
		ret.add("virtIM");
		ret.add("MobjValAsgnInst");
		ret.add("MobjVarAsgnInst");
		ret.add("MgetInstFldInst");
		ret.add("MputInstFldInst");
		ret.add("MgetStatFldInst");
		ret.add("MputStatFldInst");
		ret.add("clsForNameIT");
		ret.add("objNewInstIH");
		ret.add("objNewInstIM");
		ret.add("conNewInstIH");
		ret.add("conNewInstIM");
		ret.add("aryNewInstIH");
		ret.add("classT");
		ret.add("staticTM");
		ret.add("staticTF");
		ret.add("clinitTM");

		// hack, make constant relation VHfilter as input
		ret.add("VHfilter");

		// input relations from the client
		ret.add("checkExcludedH");
		ret.add("checkExcludedV");
		ret.add("MH");
		ret.add("MV");

		return ret;
	}

	@Override
	protected String getQueryRelation() {
		return "ptsVH";
	}

	private void generateSearchSpace() {
		try {
			PrintWriter pw = new PrintWriter(new File(Config.outDirName + File.separator + "ursa_search_space.txt"));
			// checkExcluds
			ProgramRel relExV = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedV");
			relExV.load();

			ProgramRel relExI = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedI");
			relExI.load();

			ProgramRel relExH = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedH");
			relExH.load();

			ProgramRel relExT = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedT");
			relExT.load();

			// VH
			ProgramRel relVH = (ProgramRel) ClassicProject.g().getTrgt("VH");
			relVH.load();

			for (int ts[] : relVH.getAryNIntTuples()) {
				if (!relExV.contains(ts[0])) {
					Tuple t = new Tuple(relVH, ts);
					pw.println(t.toString());
				}
			}

			// IM
			ProgramRel relIM = (ProgramRel) ClassicProject.g().getTrgt("IM");
			relIM.load();

			for (int ts[] : relIM.getAryNIntTuples()) {
				if (!relExI.contains(ts[0])) {
					Tuple t = new Tuple(relIM, ts);
					pw.println(t.toString());
				}
			}

			pw.flush();
			pw.close();
		} catch (FileNotFoundException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	protected Set<Tuple> generateFinalQueries(String queryFile) {
		this.generateSearchSpace();
		DomF domF = (DomF) ClassicProject.g().getTrgt("F");
		DomH domH = (DomH) ClassicProject.g().getTrgt("H");
		boolean usePtsVH = true;

		try {
			Set<Tuple> queries = new HashSet<Tuple>();
			PrintWriter pw = new PrintWriter(new File(queryFile));

			if (usePtsVH) {
				// VH
				{
					ProgramRel checkExcludedV = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedV");
					ProgramRel checkExcludedH = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedH");
					checkExcludedV.load();
					checkExcludedH.load();

					ProgramRel vh = (ProgramRel) ClassicProject.g().getTrgt("VH");
					vh.load();
					for (int[] indices : vh.getAryNIntTuples()) {
						Quad h = (Quad) domH.get(indices[1]);
						if (checkExcludedV.contains(indices[0]) || checkExcludedH.contains(indices[1]))
							continue;
						if (h.getOperator() instanceof New) {
							String cl = New.getType(h).getType().toString();
							if (cl.equals("java.lang.StringBuilder") || cl.equals("java.lang.StringBuffer")) {
								continue;
							}
						}
						Tuple t = new Tuple(vh, indices);
						pw.println(t);
						queries.add(t);
					}
				}

				// IM
				{
					ProgramRel checkExcludedI = (ProgramRel) ClassicProject.g().getTrgt("checkExcludedI");
					checkExcludedI.load();
					ProgramRel im = (ProgramRel) ClassicProject.g().getTrgt("IM");
					im.load();
					for (int[] indices : im.getAryNIntTuples()) {
						if (checkExcludedI.contains(indices[0]))
							continue;
						Tuple t = new Tuple(im, indices);
						pw.println(t);
						queries.add(t);
					}

				}

			} else {

				// VH
				{
					ProgramRel vh = (ProgramRel) ClassicProject.g().getTrgt("VH");
					vh.load();
					for (int[] indices : vh.getAryNIntTuples()) {
						Quad h = (Quad) domH.get(indices[1]);
						if (h.getOperator() instanceof New) {
							String cl = New.getType(h).getType().toString();
							if (cl.equals("java.lang.StringBuilder") || cl.equals("java.lang.StringBuffer")) {
								continue;
							}
						}
						Tuple t = new Tuple(vh, indices);
						pw.println(t);
						queries.add(t);
					}
				}

				// FH
				{
					ProgramRel fh = (ProgramRel) ClassicProject.g().getTrgt("FH");
					fh.load();
					for (int[] indices : fh.getAryNIntTuples()) {
						Tuple t = new Tuple(fh, indices);
						pw.println(t);
						queries.add(t);
					}

				}

				// HFH
				{
					ProgramRel hfh = (ProgramRel) ClassicProject.g().getTrgt("HFH");
					hfh.load();
					for (int[] indices : hfh.getAryNIntTuples()) {
						jq_Field f = domF.get(indices[1]);
						if (f != null)
							if (f.getDeclaringClass().toString().equals("java.lang.Throwable")) {
								continue;
							}
						Tuple t = new Tuple(hfh, indices);
						pw.println(t);
						queries.add(t);
					}

				}

				// IM
				{
					ProgramRel im = (ProgramRel) ClassicProject.g().getTrgt("IM");
					im.load();
					for (int[] indices : im.getAryNIntTuples()) {
						Tuple t = new Tuple(im, indices);
						pw.println(t);
						queries.add(t);
					}

				}
			}

			pw.flush();
			pw.close();
			return queries;
		} catch (FileNotFoundException e) {
			throw new RuntimeException(e);
		}

	}

	@Override
	protected String[] getConfigFiles() {

		// String chordMain = System.getenv("CHORD_MAIN");

		String chordIncubator = System.getenv("CHORD_INCUBATOR");
		String cipaConfig = chordIncubator + File.separator + "src/chord/analyses/mln/cipa/cipa-0cfa-dlog_XZ89_.config";
		String ptsConfig = chordIncubator + File.separator + "src/chord/analyses/mln/cipa/cipa-pts-dlog_XZ89_.config";

		String[] configFiles = new String[] { cipaConfig, ptsConfig };
		return configFiles;

	}

	@Override
	protected void genTasks() {
		tasks = new ArrayList<ITask>();

		tasks.add(ClassicProject.g().getTask("cipa-0cfa-dlog_XZ89_"));

		tasks.add(ClassicProject.g().getTask("cipa-pts-dlog_XZ89_"));
	}

	private String getClient() {
		String clientStr = null;
		clientStr = "pts";
		return clientStr;
	}

	/**
	 * Run 0-cfa
	 */
	@Override
	protected void runBaseCase() {

		for (ITask t : tasks) {
			ClassicProject.g().resetTaskDone(t);
			ClassicProject.g().runTask(t);
		}
	}

	private Quad getH(Ctxt c) {
		if (c.length() == 0)
			return null;
		return c.get(0);
	}

	@Override
	protected void readSettings() {
		super.readSettings();
		String clientStr = System.getProperty("chord.mln.client", "pts");

		this.classifierKind = System.getProperty("chord.ursa.classifier", "dynamic");

		System.setProperty("chord.ctxt.kind", "co");
	}

	@Override
	protected List<Tuple> getAxiomTuples() {
		List<Tuple> axiomTuples = new ArrayList<Tuple>();
		axiomTuples.add(new Tuple(pRel("rootM"), new int[] { 0 }));
		axiomTuples.add(new Tuple(pRel("reachableM"), new int[] { 0 }));
		return axiomTuples;
	}

	// manual labels
	private boolean ifFollowDynamicJspider(Tuple t) {
		if (!t.getRelName().equals("IM") && !t.getRelName().equals("VH"))
			return false;
		Dom dom1 = t.getDomains()[0];
		Dom dom2 = t.getDomains()[1];
		int indices[] = t.getIndices();
		String str1 = dom1.toUniqueString(indices[0]);
		String str2 = dom2.toUniqueString(indices[1]);
		// IMs
		if (t.getRelName().equals("IM")) {
			// IM(6394,2280)
			if (str1.equals(
					"3!registerEvent:(Ljava/net/URL;Lnet/javacoding/jspider/core/event/CoreEvent;)V@net.javacoding.jspider.core.impl.AgentImpl")
					&& str2.equals(
							"accept:(Ljava/net/URL;Lnet/javacoding/jspider/core/event/CoreEventVisitor;)V@net.javacoding.jspider.core.event.impl.URLSpideredErrorEvent"))
				return false;
		}
		// VH
		if (t.getRelName().equals("VH")) {
			// VH(17206,1660)
			if (str1.equals(
					"T4!getConfiguration:()Lnet/javacoding/jspider/core/util/config/JSpiderConfiguration;@net.javacoding.jspider.core.util.config.ConfigurationFactory")
					&& str2.equals(
							"6!getConfiguration:()Lnet/javacoding/jspider/core/util/config/JSpiderConfiguration;@net.javacoding.jspider.core.util.config.ConfigurationFactory")) {
				return false;
			}
		}
		return true;
	}

	private boolean ifFollowDynamicHedc(Tuple t) {
		if (!t.getRelName().equals("IM") && !t.getRelName().equals("VH"))
			return false;
		Dom dom1 = t.getDomains()[0];
		Dom dom2 = t.getDomains()[1];
		int indices[] = t.getIndices();
		String str1 = dom1.toUniqueString(indices[0]);
		String str2 = dom2.toUniqueString(indices[1]);
		// IMs
		if (t.getRelName().equals("IM")) {
			// IM(1089.*)
			if (str1.equals("10!match:(Lhedc/regexp/State;)Z@hedc.regexp.Regexp"))
				return false;
		}
		// VH
		if (t.getRelName().equals("VH")) {
			// VH(1567,106)
			if (str1.equals(
					"T25!makeTasks:(Ljava/util/Hashtable;Ljava/util/Date;Lhedc/MetaSearchRequest;)Ljava/util/List;@hedc.TaskFactory")
					&& str2.equals("33!<clinit>:()V@hedc.TaskFactory"))
				return false;
		}
		return true;

	}

	private boolean ifFollowDynamicFtp(Tuple t) {
		if (!t.getRelName().equals("IM") && !t.getRelName().equals("VH"))
			return false;
		Dom dom1 = t.getDomains()[0];
		Dom dom2 = t.getDomains()[1];
		int indices[] = t.getIndices();
		String str1 = dom1.toUniqueString(indices[0]);
		String str2 = dom2.toUniqueString(indices[1]);
		// IMs
		if (t.getRelName().equals("IM")) {
			Quad qi = (Quad) t.getValue(0);
			jq_Method m = (jq_Method) t.getValue(1);
			// IM(15234.*)
			if (str1.equals(
					"22!service:(Lorg/apache/ftpserver/FtpRequestImpl;Lorg/apache/ftpserver/FtpWriter;)V@org.apache.ftpserver.RequestHandler"))
				return false;
			// IM(14581,*), actually any invocation related to
			// org.apache.ftpserver.ftplet.Configuration
			if (Invoke.getMethod(qi).getMethod().getDeclaringClass().toString()
					.equals("org.apache.ftpserver.ftplet.Configuration"))
				return false;
			// IM(16759,4642), actullay any method related to LogFactory
			if (m.getDeclaringClass().toString().equals("org.apache.commons.logging.LogFactory"))
				return false;
			// IM(15224,.*)
			if (str1.equals(
					"22!service:(Lorg/apache/ftpserver/FtpRequestImpl;Lorg/apache/ftpserver/FtpWriter;)V@org.apache.ftpserver.RequestHandler"))
				return false;
		}
		// VH
		if (t.getRelName().equals("VH")) {
			// VH(33013,3054)
			if (str1.equals("T1!getUser:()Lorg/apache/ftpserver/ftplet/User;@org.apache.ftpserver.FtpRequestImpl")
					&& str2.equals("1!reinitialize:()V@org.apache.ftpserver.FtpRequestImpl"))
				return false;
		}
		return true;
	}

	private boolean ifFollowDynamicWeblech(Tuple t) {
		if (!t.getRelName().equals("IM") && !t.getRelName().equals("VH"))
			return false;
		Dom dom1 = t.getDomains()[0];
		Dom dom2 = t.getDomains()[1];
		int indices[] = t.getIndices();
		String str1 = dom1.toUniqueString(indices[0]);
		String str2 = dom2.toUniqueString(indices[1]);
		// IMs
		if (t.getRelName().equals("IM")) {
			Quad i = (Quad) t.getValue(0);
			if (i.getMethod().getDeclaringClass().toString().contains("org.apache.log4j"))
				return false;
		}
		// VH
		if (t.getRelName().equals("VH")) {
			Quad h = (Quad) t.getValue(1);
			if (h.getMethod().getDeclaringClass().toString().contains("org.apache.log4j"))
				return false;
			// VH(34710,3004)
			if (str1.equals("T1!getURL:()Ljava/net/URL;@weblech.spider.URLToDownload") && str2.equals(
					"238!extractAttributesFromTags:(Ljava/lang/String;Ljava/lang/String;Ljava/net/URL;Ljava/util/List;Ljava/util/Set;Ljava/lang/String;)V@weblech.spider.HTMLParser"))
				return false;
		}
		return true;
	}

	@Override
	protected void predict(Set<Tuple> tuples, Set<ConstraintItem> provenance, String classifierPath) {
		try {
			PrintWriter pw = new PrintWriter(new File(Config.outDirName + File.separator + "prediction.txt"));
			// always run dynamic now
			// if(this.classifierKind.equals("dynamic")){
			classifier = new DynamicAnalysisClassifier();
			// }
			// else if (this.classifierKind.equals("none"))
			// classifier = null;
			// else
			// throw new RuntimeException("Unknown classifier
			// "+this.classifierKind);
			for (Tuple t : tuples) {
				if (classifier == null)
					pw.println(t + " 0");
				else
					pw.println(t + " " + classifier.predictFalse(t, provenance));
			}
			pw.flush();
			pw.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			System.exit(1);
		}

	}

}
