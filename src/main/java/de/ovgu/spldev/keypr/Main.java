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
import guru.nidi.graphviz.engine.Format;
import guru.nidi.graphviz.engine.Graphviz;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Main {
    public static void main(String[] args) {
        KeYBridge.initialize();
        VerificationSystem verificationSystem =
                new VerificationSystem.KeY(
                        KeYBridge.Mode.AUTO,
                        KeYBridge.OptimizationStrategy.DEF_OPS,
                        Paths.get("proofRepository"));
        //verificationSystem = new VerificationSystem(Paths.get("proofRepository"));
        verifyFeatureIDEProject(Paths.get("examples/list"), verificationSystem);
    }

    private static void verifyFeatureIDEProject(@SuppressWarnings("SameParameterValue") Path path,
                                                   VerificationSystem verificationSystem) {
        Model.SoftwareProductLine spl = getSoftwareProductLine(path);
        Model.BindingGraph prunedBindingGraph = spl.program().prunedBindingGraph(spl);
        render(prunedBindingGraph.toDot(), verificationSystem.proofRepositoryPath, "prunedBindingGraph");
        Model.VerificationPlan verificationPlan =
                prunedBindingGraph.someVerificationPlan().removeDeadEnds().combineLinearSubPaths();
        render(verificationPlan.toDot(), verificationSystem.proofRepositoryPath, "verificationPlan");
        Model.VerificationAttempt verificationAttempt = verificationPlan.verificationAttempt(verificationSystem);
        verificationAttempt.verify();
        if (!verificationAttempt.isCorrect()) {
            System.out.println("Failed proofs:");
            verificationAttempt.failedProofs().forEach(System.out::println);
        }
        System.out.println(verificationAttempt.isCorrect() ? "VERIFICATION SUCCESSFUL" : "VERIFICATION FAILED");
    }

    private static Model.SoftwareProductLine getSoftwareProductLine(Path path) {
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

    static void render(String dot, Path path, String name) {
        Graphviz graph = Graphviz.fromString(dot);
        try {
            graph.render(Format.SVG).toFile(path.resolve(name + ".svg").toFile());
            graph.render(Format.PNG).toFile(path.resolve(name + ".png").toFile());
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
