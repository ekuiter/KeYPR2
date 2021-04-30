package de.ovgu.spldev.keypl;

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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class Shell {
    private final Path resultPath;
    Core.VerificationGraph verificationGraph;
    Function<String, Core.VerificationSystem> verificationSystemSupplier;
    String focusOnMethod;
    int n;
    boolean warmedUp = false;
    int run = 1;

    public Shell(Path resultPath,
                 Core.VerificationGraph verificationGraph,
                 Function<String, Core.VerificationSystem> verificationSystemSupplier,
                 String focusOnMethod, int n) {
        this.resultPath = resultPath;
        this.verificationGraph = verificationGraph;
        this.verificationSystemSupplier = verificationSystemSupplier;
        this.focusOnMethod = focusOnMethod;
        this.n = n;
        Utils.createDirectory(resultPath);
    }

    public void verify(Main.VerificationStrategy verificationStrategy) {
        List<HashMap<String, List<Integer>>> statistics = new ArrayList<>();
        StringBuilder sb = new StringBuilder();
        if (!warmedUp) {
            System.out.println("Warm-up run (" +  verificationStrategy + ")");
            Shell.verifyFeatureIDEProject(verificationSystemSupplier.apply("0"),
                    verificationGraph, verificationStrategy, focusOnMethod);
            warmedUp = true;
        }
        for (int i = 1; i <= n; i++) {
            System.out.println("Run #" + run + "." + i + " (" +  verificationStrategy + ")");
            statistics.add(Shell.verifyFeatureIDEProject(verificationSystemSupplier.apply(run + "." + i),
                    verificationGraph, verificationStrategy, focusOnMethod));
        }
        HashMap<String, List<Integer>> statisticsMap = Core.VerificationAttempt.getStatisticsMap(statistics);
        statisticsMap.forEach(
                (k, v) -> sb.append(String.format("%s,%s%n", k, v.stream()
                        .map(Object::toString).collect(Collectors.joining(",")))));
        List<Integer> totalResults = Core.VerificationAttempt.sumStatisticsMap(statisticsMap);
        String total = totalResults.stream()
                .map(Object::toString).collect(Collectors.joining(","));
        sb.append("total,").append(total);
        System.out.println(total);
        Utils.writeFile(
                resultPath.resolve(String.format("%d-%s-%d.csv", run, verificationStrategy, totalResults.get(1))),
                sb.toString());
        run++;
    }

    static HashMap<String, List<Integer>> verifyFeatureIDEProject(
            Core.VerificationSystem verificationSystem,
            Core.VerificationGraph verificationGraph,
            Main.VerificationStrategy verificationStrategy,
            String focusOnMethod) {
        if (verificationStrategy instanceof Main.VerificationStrategy.FamilyBased)
            return verifyFamilyBased(
                    ((Main.VerificationStrategy.FamilyBased) verificationStrategy).path, verificationSystem);
        Utils.render(verificationGraph.toDot(), verificationSystem.path, "verificationGraph");
        Core.VerificationPlan verificationPlan = verificationStrategy.verificationPlan();
        Utils.render(verificationPlan.toDot(), verificationSystem.path, "verificationPlan");
        Core.VerificationAttempt verificationAttempt = verificationPlan.verificationAttempt(verificationSystem);
        verificationAttempt.verify(focusOnMethod);
        if (!verificationAttempt.isCorrect()) {
            System.out.println("Failed proofs:");
            verificationAttempt.failedProofs().forEach(System.out::println);
        }
        return verificationAttempt.getStatisticsMap(verificationGraph.completeNodeOccurrences);
    }

    static HashMap<String, List<Integer>> verifyFamilyBased(Path path, Core.VerificationSystem verificationSystem) {
        return KeYBridge.proveAllContracts(path.toFile(),
                verificationSystem.path, verificationSystem.settings);
    }

    static Core.SoftwareProductLine getSoftwareProductLine(Path path) {
        LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
        IFeatureModel featureModel = FeatureModelManager.load(path.resolve("model.xml"));
        CNF cnf = new FeatureModelFormula(featureModel).getCNF();
        return new Core.SoftwareProductLine(
                featureModel.getFeatureOrderList(), // this omits abstract features!
                LongRunningWrapper.runMethod(new AllConfigurationGenerator(cnf)).stream()
                        .map(literalSet -> new HashSet<>(cnf.getVariables().convertToString(literalSet)))
                        .collect(Collectors.toSet()),
                parseMethods(path));
    }

    static Set<Core.Method> parseMethods(Path path) {
        Set<String> methodNames = Stream.of("original").collect(Collectors.toSet());
        Set<Core.Method> methods = new HashSet<>();
        Consumer<Path> walker = directory -> {
            String feature = directory.getFileName().toString();
            if (feature.equals("features"))
                return;
            try {
                Files.walk(path.resolve("features").resolve(feature)).forEach(file -> {
                    try {
                        CompilationUnit compilationUnit = StaticJavaParser.parse(file);
                        new VoidVisitorAdapter<Set<Core.Method>>() {
                            @Override
                            public void visit(MethodDeclaration n, Set<Core.Method> methods) {
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
                                    signatures.add(new Core.Signature(n.getDeclarationAsString())
                                            .withName("original").toString());
                                methods.add(new Core.Method(feature, n.getName().asString(),
                                        new Core.HoareTriple(contract[0],
                                                new DefaultPrettyPrinter(new DefaultPrinterConfiguration()).print(n),
                                                contract[1], contract[2],
                                                signatures, implementationCalls, contractCalls)));
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
