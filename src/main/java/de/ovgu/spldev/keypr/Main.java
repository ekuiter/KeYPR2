package de.ovgu.spldev.keypr;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.printer.DefaultPrettyPrinter;
import com.github.javaparser.printer.configuration.DefaultPrinterConfiguration;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AllConfigurationGenerator;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.uka.ilkd.key.strategy.StrategyProperties;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Main {
    // binding graphs represent a continuum of possible analyses. here are some well-known supported ones:
    @SuppressWarnings("unused")
    enum AnalysisKind {ANY, OPTIMIZED_PRODUCT_BASED, FAMILY_BASED, FEATURE_FAMILY_BASED}

    // set path to FeatureIDE project that should be verified
    static Path path;
    // set KeY parameters and target directory
    static Supplier<VerificationSystem.KeY> verificationSystemSupplier = () -> {
        HashMap<String, String> strategyProperties = new HashMap<>();
        strategyProperties.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        strategyProperties.put(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
        strategyProperties.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        HashMap<String, String> partialProofStrategyProperties = new HashMap<>();
        partialProofStrategyProperties.put(
                StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
        return new VerificationSystem.KeY(
                new KeYBridge.Settings(KeYBridge.Mode.AUTO, strategyProperties, partialProofStrategyProperties),
                Paths.get("caseStudy/proofRepository"));
    };
    // set kind of performed analysis
    static AnalysisKind analysisKind;
    // only verify the method "<feature>::<name>", useful for debugging
    static String focusOnMethod = null;
    // number of repetitions for evaluation purposes
    static int N = 0;

    // case study: optimized product-based
    static {
        path = Paths.get("caseStudy/IntList");
        analysisKind = AnalysisKind.OPTIMIZED_PRODUCT_BASED;
    }

//    // case study: feature-family-based
    static {
        path = Paths.get("caseStudy/IntList");
        analysisKind = AnalysisKind.FEATURE_FAMILY_BASED;
    }

    // case study: family-based (code generated from IntList project with FeatureIDE/FeatureHouse)
    static {
        path = Paths.get("caseStudy/IntListMetaProduct");
        analysisKind = AnalysisKind.FAMILY_BASED;
    }

    public static void main(String[] args) {
        List<HashMap<String, List<Integer>>> statistics = new ArrayList<>();
        // warm-up run
        verifyFeatureIDEProject(path, verificationSystemSupplier.get(), analysisKind, focusOnMethod);
        // actual evaluation
        for (int i = 0; i < N; i++)
            statistics.add(verifyFeatureIDEProject(
                    path, verificationSystemSupplier.get(), analysisKind, focusOnMethod));
        Model.VerificationAttempt.getStatisticsMap(statistics).forEach(
                (k, v) -> System.out.printf("%s,%s%n", k, v.stream()
                        .map(Object::toString).collect(Collectors.joining(","))));
    }

    @SuppressWarnings("SameParameterValue")
    static HashMap<String, List<Integer>> verifyFeatureIDEProject(
            Path path, VerificationSystem.KeY verificationSystem, AnalysisKind analysisKind, String focusOnMethod) {
        if (analysisKind.equals(AnalysisKind.FAMILY_BASED))
            return verifyFamilyBased(path, verificationSystem);
        return verifyFeatureIDEProject(path, verificationSystem,
                analysisKind.equals(AnalysisKind.OPTIMIZED_PRODUCT_BASED)
                        ? Model.BindingGraph::minPartialProofReuseVerificationPlan
                        : analysisKind.equals(AnalysisKind.FEATURE_FAMILY_BASED)
                        ? Model.BindingGraph::maxPartialReuseVerificationPlan
                        : Model.BindingGraph::someVerificationPlan,
                focusOnMethod);
    }

    static HashMap<String, List<Integer>> verifyFeatureIDEProject(
            @SuppressWarnings("SameParameterValue") Path path, VerificationSystem verificationSystem,
            Function<Model.PrunedBindingGraph, Model.VerificationPlan> fn,
            @SuppressWarnings("SameParameterValue") String focusOnMethod) {
        Model.SoftwareProductLine spl = getSoftwareProductLine(path);
        Model.PrunedBindingGraph prunedBindingGraph = spl.program().prunedBindingGraph(spl);
        Utils.render(prunedBindingGraph.toDot(), verificationSystem.proofRepositoryPath, "prunedBindingGraph");
        Model.VerificationPlan verificationPlan = fn.apply(prunedBindingGraph);
        Utils.render(verificationPlan.toDot(), verificationSystem.proofRepositoryPath, "verificationPlan");
        Model.VerificationAttempt verificationAttempt = verificationPlan.verificationAttempt(verificationSystem);
        verificationAttempt.verify(focusOnMethod);
        if (!verificationAttempt.isCorrect()) {
            System.out.println("Failed proofs:");
            verificationAttempt.failedProofs().forEach(System.out::println);
        }
        System.out.println(verificationAttempt.isCorrect() ? "VERIFICATION SUCCESSFUL" : "VERIFICATION FAILED");
        return verificationAttempt.getStatisticsMap(prunedBindingGraph.getCompleteNodeOccurrences());
    }

    static HashMap<String, List<Integer>> verifyFamilyBased(Path path, VerificationSystem.KeY verificationSystem) {
        return KeYBridge.proveAllContracts(path.toFile(),
                verificationSystem.proofRepositoryPath, verificationSystem.settings);
    }

    static Model.SoftwareProductLine getSoftwareProductLine(Path path) {
        LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
        IFeatureModel featureModel = FeatureModelManager.load(path.resolve("model.xml"));
        CNF cnf = new FeatureModelFormula(featureModel).getCNF();
        return new Model.SoftwareProductLine(
                featureModel.getFeatureOrderList(), // this omits abstract features!
                LongRunningWrapper.runMethod(new AllConfigurationGenerator(cnf)).stream()
                        .map(literalSet -> new HashSet<>(cnf.getVariables().convertToString(literalSet)))
                        .collect(Collectors.toSet()),
                parseMethods(path));
    }

    static Set<Model.Method> parseMethods(Path path) {
        Set<String> methodNames = Stream.of("original").collect(Collectors.toSet());
        Set<Model.Method> methods = new HashSet<>();
        Consumer<Path> walker = directory -> {
            String feature = directory.getFileName().toString();
            if (feature.equals("features"))
                return;
            try {
                Files.walk(path.resolve("features").resolve(feature)).forEach(file -> {
                    try {
                        CompilationUnit compilationUnit = StaticJavaParser.parse(file);
                        new VoidVisitorAdapter<Set<Model.Method>>() {
                            @Override
                            public void visit(MethodDeclaration n, Set<Model.Method> methods) {
                                super.visit(n, methods);
                                Set<String> implementationCalls = new HashSet<>(), contractCalls = new HashSet<>();
                                Node.BreadthFirstIterator bfi = new Node.BreadthFirstIterator(n);
                                final String[] contract = {"true", "true", "\\everything"};
                                Set<String> signatures = new HashSet<>();
                                n.getAllContainedComments().forEach(comment -> {
                                    String content = comment.getContent().trim();
                                    if (content.startsWith("CALLS"))
                                        signatures.add(content.split("CALLS", 2)[1]);
                                });
                                while (bfi.hasNext()) {
                                    Node n2 = bfi.next();
                                    if (n2 instanceof MethodCallExpr)
                                        implementationCalls.add(((MethodCallExpr) n2).getName().asString());
                                }
                                n.getComment().ifPresent(comment -> {
                                    if (comment.getContent().contains("\\original"))
                                        contractCalls.add("original");
                                    Matcher matcher = Pattern.compile("@.*requires(.*)").matcher(comment.getContent());
                                    if (matcher.find())
                                        contract[0] = matcher.group(1).trim();
                                    if (contract[0].endsWith(";"))
                                        contract[0] = contract[0].substring(0, contract[0].length() - 1);
                                    matcher = Pattern.compile("@.*ensures(.*)").matcher(comment.getContent());
                                    if (matcher.find())
                                        contract[1] = matcher.group(1).trim();
                                    if (contract[1].endsWith(";"))
                                        contract[1] = contract[1].substring(0, contract[1].length() - 1);
                                    matcher = Pattern.compile("@.*assignable(.*)").matcher(comment.getContent());
                                    if (matcher.find())
                                        contract[2] = matcher.group(1).trim();
                                    if (contract[2].endsWith(";"))
                                        contract[2] = contract[2].substring(0, contract[2].length() - 1);
                                    comment.remove();
                                });
                                methodNames.add(n.getName().asString());
                                // Assumption: If class A != class B and there are methods A.m1 and B.m2, m1 != m2.
                                // Basically, this forbids late binding / polymorphism.
                                if (contractCalls.contains("original"))
                                    signatures.add(new VerificationSystem.KeY.Signature(n.getDeclarationAsString())
                                            .withName("original").toString());
                                methods.add(new Model.Method(feature, n.getName().asString(),
                                        new VerificationSystem.KeY.HoareTriple(signatures,
                                                implementationCalls, contractCalls, contract[0],
                                                new DefaultPrettyPrinter(new DefaultPrinterConfiguration()).print(n),
                                                contract[1], contract[2])));
                            }
                        }.visit(compilationUnit, methods);
                    } catch (IOException ignored) {
                    }
                });
            } catch (IOException ignored) {
            }
        };
        try {
            Files.walk(path.resolve("features"), 1).forEach(walker);
        } catch (IOException ignored) {
        }
        methods.forEach(method -> method.hoareTriple.implementationCalls().retainAll(methodNames));
        return methods;
    }
}
