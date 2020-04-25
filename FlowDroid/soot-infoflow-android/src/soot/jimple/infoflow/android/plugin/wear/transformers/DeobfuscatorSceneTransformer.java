package soot.jimple.infoflow.android.plugin.wear.transformers;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Local;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.jimple.infoflow.android.plugin.wear.analysis.AnalysisUtil;
import soot.jimple.infoflow.android.plugin.wear.deofucator.CallbacksDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.CapabilityApiDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.CapabilityClientDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataApiDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataClientDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataEventDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataItemDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataMapDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.DataMapItemDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.Deofuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.MessageApiDeofuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.MessageClientDeofuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.MessageEventDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.PutDMRDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.PutDRDeobfuscator;
import soot.jimple.infoflow.android.plugin.wear.deofucator.WearableServiceObfuscator;
import soot.jimple.infoflow.plugin.wear.extras.ExtraTypes;
import soot.util.Chain;

public class DeobfuscatorSceneTransformer extends SceneTransformer {

	private static AnalysisUtil utilInstance = AnalysisUtil.getInstance();
	private List<SootClass> relevantComponents;
	private final Logger logger = LoggerFactory.getLogger(getClass());
	String apkFilePath;
	int nonFound = 0;

	public DeobfuscatorSceneTransformer(String targetAPKFile) {
		apkFilePath = targetAPKFile;
	}

	@Override
	protected void internalTransform(String phaseName, Map<String, String> options) {

		relevantComponents = getRelevantComponents();
		boolean obf = deobfuscateLibraryClasses();
		if (obf == true) {
			deobfuscateComponents(relevantComponents);
		}

		if (relevantComponents.size() == 0) {
			logger.info("Program terminated, no components to instrument found");
			System.exit(0);
		}

	}

	public List<SootClass> getComponentsToInstrument() {
		return relevantComponents;

	}

	/**
	 * return true if the class extend from WearableListenerService or implements a
	 * Listener interface
	 * 
	 * @param sc
	 * @return
	 */
	private boolean hasCallbacks(SootClass sc) {
		if (sc.getSuperclass().toString().equals(ExtraTypes.WEARABLE_LISTENER_SERVICE))
			return true;
		if (sc.getInterfaceCount() > 0) {
			Chain<SootClass> interfaces = sc.getInterfaces();
			for (SootClass interf : interfaces) {
				switch (interf.getName()) {
				case ExtraTypes.DATA_LISTENER:
					return true;
				case ExtraTypes.ON_DATA_CHANGED_LISTENER:
					return true;
				case ExtraTypes.MESSAGE_LISTENER:
					return true;
				case ExtraTypes.ON_MESSAGE_RECEIVED_LISTENER:
					return true;
				case ExtraTypes.GOOGLE_API_CLIENT_CALLBACKS:
					return true;
				case ExtraTypes.CAPABILITY_API_LISTENER:
					return true;
				case ExtraTypes.CAPABILITY_CLIENT_ON_CHANGED_LISTENER:
					return true;
				default:
					return false;
				}
			}
		}

		return false;
	}

	private void deobfuscateComponents(List<SootClass> components) {
		Deofuscator deof = new Deofuscator();
		List<SootClass> processed = new ArrayList<>();
		for (int j = 0; j < components.size(); j++) {
			SootClass sc = components.get(j);

			if (processed.contains(sc))
				continue;
			else
				processed.add(sc);

			if (hasCallbacks(sc))
				deof.deobfuscateCallbacks(sc);

			List<SootMethod> processedMethods = new ArrayList<>();
			for (Iterator<SootMethod> it = sc.getMethods().listIterator(); it.hasNext();) {
				SootMethod sm = it.next();

				if (processedMethods.contains(sm))
					continue;
				else
					processedMethods.add(sm);

				if (sm.isConcrete() && utilInstance.instrumentationNeeded(sm)) {
					deof.deofucateMethod(sm);
				}
			}
		}
	}

	private boolean deobfuscateLibraryClasses() {

		boolean obfuscated = false;
		List<Boolean> obfChecker = new ArrayList<>();
		SootClass dataClientClass = Scene.v().getSootClass(ExtraTypes.DATA_CLIENT);
		if (dataClientClass != null && !dataClientClass.isPhantom()) {
			DataClientDeobfuscator dcDeob = DataClientDeobfuscator.getInstance();
			obfuscated = dcDeob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass dataClass = Scene.v().getSootClass(ExtraTypes.DATA_API);
		if (dataClass != null && !dataClass.isPhantom()) {
			DataApiDeobfuscator daDeob = DataApiDeobfuscator.getInstance();
			obfuscated = daDeob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass pdmrClass = Scene.v().getSootClass(ExtraTypes.PUT_DATA_MAP_REQUEST);
		if (pdmrClass != null && !pdmrClass.isPhantom()) {
			PutDMRDeobfuscator deob = PutDMRDeobfuscator.getInstance();
			obfuscated = deob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass pdrClass = Scene.v().getSootClass(ExtraTypes.PUT_DATA_REQUEST);
		if (pdrClass != null && !pdrClass.isPhantom()) {
			PutDRDeobfuscator deob = PutDRDeobfuscator.getInstance();
			obfuscated = deob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		// generate sources for DataMaps
		SootClass sClass = Scene.v().getSootClass(ExtraTypes.DATA_MAP);
		if (sClass != null && !sClass.isPhantom()) {
			DataMapDeobfuscator deob = DataMapDeobfuscator.getInstance();
			obfuscated = deob.deobfuscateDataMap();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass ditemClass = Scene.v().getSootClass(ExtraTypes.DATA_ITEM);
		if (ditemClass != null && !ditemClass.isPhantom()) {
			DataItemDeobfuscator dieobf = DataItemDeobfuscator.getInstance();
			obfuscated = dieobf.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass dEventClass = Scene.v().getSootClass(ExtraTypes.DATA_EVENT);
		if (dEventClass != null && !dEventClass.isPhantom()) {
			DataEventDeobfuscator deobf = DataEventDeobfuscator.getInstance();
			obfuscated = deobf.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass dmapitemClass = Scene.v().getSootClass(ExtraTypes.DATA_MAP_ITEM);
		if (dmapitemClass != null && !dmapitemClass.isPhantom()) {
			DataMapItemDeobfuscator dmapItemobf = DataMapItemDeobfuscator.getInstance();
			obfuscated = dmapItemobf.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass mcClass = Scene.v().getSootClass(ExtraTypes.MESSAGE_CLIENT);
		if (mcClass != null && !mcClass.isPhantom()) {
			MessageClientDeofuscator messClientDeobf = MessageClientDeofuscator.getInstance();
			obfuscated = messClientDeobf.deofuscateMessageclient();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass maClass = Scene.v().getSootClass(ExtraTypes.MESSAGE_API);
		if (maClass != null && !maClass.isPhantom()) {
			MessageApiDeofuscator messApiDeof = MessageApiDeofuscator.getInstance();
			obfuscated = messApiDeof.deofuscateMessageApi();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass wsClass = Scene.v().getSootClass(ExtraTypes.WEARABLE_LISTENER_SERVICE);
		if (wsClass != null && !wsClass.isPhantom()) {
			WearableServiceObfuscator wsDeob = WearableServiceObfuscator.getInstance();
			obfuscated = wsDeob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass messageClass = Scene.v().getSootClass(ExtraTypes.MESSAGE_EVENT);
		if (messageClass != null && !messageClass.isPhantom()) {
			MessageEventDeobfuscator meDeobf = MessageEventDeobfuscator.getInstance();
			obfuscated = meDeobf.deofuscateMessageEvent();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass callbacks = Scene.v().getSootClass(ExtraTypes.GOOGLE_API_CLIENT_CALLBACKS);
		if (callbacks != null && !callbacks.isPhantom()) {
			CallbacksDeobfuscator cdeob = CallbacksDeobfuscator.getInstance();
			obfuscated = cdeob.deobfuscateGoogleApiClient();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass capaClient = Scene.v().getSootClass(ExtraTypes.CAPABILITY_CLIENT_ON_CHANGED_LISTENER);
		if (capaClient != null && !capaClient.isPhantom()) {
			CapabilityClientDeobfuscator ccdeob = CapabilityClientDeobfuscator.getInstance();
			obfuscated = ccdeob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		SootClass capi = Scene.v().getSootClass(ExtraTypes.CAPABILITY_API_LISTENER);
		if (capi != null && !capi.isPhantom()) {
			CapabilityApiDeobfuscator capideob = CapabilityApiDeobfuscator.getInstance();
			obfuscated = capideob.deobfuscateClass();
			obfChecker.add(obfuscated);
		} else
			nonFound++;

		obfuscated = false;
		for (Boolean b : obfChecker) {
			if (b == true)
				obfuscated = true;
		}
		return obfuscated;
	}

	private List<SootClass> getRelevantComponents() {

		List<SootClass> toInstrument = new ArrayList<SootClass>();
		List<String> relevantClasses = new ArrayList<String>(Arrays.asList(ExtraTypes.classesForInstrumentation));
		for (SootClass sClass : Scene.v().getApplicationClasses()) {

			if (sClass.getPackageName().startsWith("com.google.android.gms")
					|| sClass.getPackageName().startsWith("android.support.wearable") || sClass.isJavaLibraryClass()
					|| utilInstance.isAndroidLibrary(sClass))
				continue;

			Boolean searchMethods = true;
			// we only want to load classes defined by the user
			for (SootField f : sClass.getFields()) {
				if (relevantClasses.contains(f.getType().toString())) {
					toInstrument.add(sClass);
					searchMethods = false;
					break;
				}
			}
			if (searchMethods) {
				for (SootMethod sm : sClass.getMethods()) {
					if (sm.isConcrete()) {
						Chain<Local> locals = sm.retrieveActiveBody().getLocals();
						for (Local local : locals) {
							if (relevantClasses.contains(local.getType().toString())) {
								toInstrument.add(sClass);
								break;
							}
						}
					}
				}
			}

		}
		return (toInstrument);

	}

}
