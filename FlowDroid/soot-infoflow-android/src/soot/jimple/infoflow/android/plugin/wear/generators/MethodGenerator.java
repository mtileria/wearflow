package soot.jimple.infoflow.android.plugin.wear.generators;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import soot.Body;
import soot.Local;
import soot.Modifier;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.VoidType;
import soot.jimple.Jimple;
import soot.jimple.JimpleBody;

public class MethodGenerator {

	private SootClass sClass;

	private Body body;
	private Local thisLocal;
	private SootMethod methodToGenerate;
	private List<Local> paramsList;


	/**
	 * Default constructor
	 * 
	 * @param sClass
	 *            The generated methods will be added to sClass
	 * @param methodToGenerate
	 *            The method that is being generated
	 */
	public MethodGenerator(SootClass sClass) {
		this.setsClass(sClass);
		paramsList = new ArrayList<>();
		// this.methodToGenerate = methodToGenerate;
	}
	
	public MethodGenerator() {
	}
	

	public SootClass getsSootClass() {
		return sClass;
	}

	public void setsClass(SootClass sClass) {
		this.sClass = sClass;
	}

	public SootMethod generateEmptySink() {
		SootClass tmpClass = Scene.v().getSootClass("java.lang.String");
		return (generateEmptyMethod("sinkExplicit", VoidType.v(),tmpClass.getType()));	
	}
	

	/**
	 * Generate an empty public method with the given signature and returns it
	 * 
	 * @param methodName
	 *            the name to give to the method
	 * @param returnType
	 *            the return type of the method
	 * @param types
	 *            parameter types of the method generated
	 * @return the generated method
	 */
	protected SootMethod generateEmptyMethod(String methodName, Type returnType, Type... types) {


		SootMethod sMethod = new SootMethod(methodName, Arrays.asList(types), returnType, Modifier.STATIC);
		this.methodToGenerate = sMethod;
		sClass.addMethod(sMethod);
		createEmptyBody(sMethod);
		//createThisLocalAndRef(sMethod);
		// generateParameters(sMethod, types);

		return sMethod;
	}

	/**
	 * Generate an empty public method with the given signature and returns it
	 * 
	 * @param methodName
	 *            the name to give to the method
	 * @param returnType
	 *            the return type of the method
	 * @param types
	 *            parameter types of the method generated
	 * @param modifier
	 *            modifier of the method
	 * @return the generated method
	 */
	protected SootMethod generateEmptyMethod(String methodName, Type returnType, int modifier, Type... types) {

		SootMethod sMethod = new SootMethod(methodName, Arrays.asList(types), returnType, modifier);
		this.methodToGenerate = sMethod;
		sClass.addMethod(sMethod);
		createEmptyBody(sMethod);
		//if (modifier != Modifier.STATIC)
		//	createThisLocalAndRef(sMethod);
		//generateParameters(sMethod, types);

		return sMethod;
	}
	
	/**
	 * Create an empty body for the sMethod requested and returns it
	 * 
	 * @param sMethod
	 * @return An empty body for the method requested
	 */
	protected Body createEmptyBody(SootMethod sMethod) {
		JimpleBody body = Jimple.v().newBody(sMethod);
		sMethod.setActiveBody(body);
		return body;
	}

	
	protected void addCallToSuper(String superMethod) {
		Body body = methodToGenerate.retrieveActiveBody();
		body.getUnits().add(Jimple.v().newInvokeStmt(
				Jimple.v().newSpecialInvokeExpr(thisLocal, Scene.v().getMethod(superMethod).makeRef(), paramsList)));
	}

	protected Body getBody() {
		return body;
	}

	protected void setBody(Body body) {
		this.body = body;
	}

	public Local getThisLocal() {
		return thisLocal;
	}

	public void setThisLocal(Local thisLocal) {
		this.thisLocal = thisLocal;
	}


	/**
	 * Handle the reference for this into the generated method. This method create a
	 * local to host the this reference and add all to the body units.
	 * 
	 * @param sMethod
	 *            the method where to create the ref
	
	private void createThisLocalAndRef(SootMethod sMethod) {
		Body body = sMethod.retrieveActiveBody();

		// creating this local
		thisLocal = localFactory.genLocal(sClass.getType());
		body.getLocals().add(thisLocal);

		// add this ref
		body.getUnits().add(Jimple.v().newIdentityStmt(thisLocal, Jimple.v().newThisRef(sClass.getType())));

	} 
	
	private void generateParameters(SootMethod sMethod, Type... types) {
		Body body = sMethod.retrieveActiveBody();
		Chain<Unit> units = body.getUnits();
		List<Local> paramList = new ArrayList<Local>();

		int j = 0;
		for (Type paramType : types) {

			Local param = localFactory.genLocal(paramType);

			body.getLocals().add(param);
			units.add(Jimple.v().newIdentityStmt(param, Jimple.v().newParameterRef(paramType, j)));
			paramList.add(param);
			j++;

		}

		this.paramsList = paramList;

	}*/
 
}
