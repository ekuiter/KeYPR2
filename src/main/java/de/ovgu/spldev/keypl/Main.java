package de.ovgu.spldev.keypl;

import de.uka.ilkd.key.strategy.StrategyProperties;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args) {
        if (args.length < 2 || args.length > 3) {
            System.out.println("As first argument, pass feature, product, " +
                    "feature-product, feature-family, feature-family-all, or family.\n" +
                    "As second argument, pass number of repetitions.\n" +
                    "As third argument, pass method to focus on (optional).");
            return;
        }
        Utils.deleteDirectory(Paths.get("caseStudy/evaluation-" + args[0]));
        Core.ProofGraph proofGraph = // path to FeatureIDE project that should be verified
                Shell.getSoftwareProductLine(Paths.get("caseStudy/IntList")).proofGraph();
        Shell shell = new Shell(
                Paths.get("caseStudy/evaluation-" + args[0] + "/results"),
                proofGraph,
                run -> {
                    HashMap<String, String> strategyProperties = new HashMap<>();
                    strategyProperties.put(
                            StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
                    strategyProperties.put(
                            StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
                    strategyProperties.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                            StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
                    HashMap<String, String> partialProofStrategyProperties = new HashMap<>();
                    partialProofStrategyProperties.put(
                            StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
                    return new Core.VerificationSystem(
                            Paths.get("caseStudy/evaluation-" + args[0]).resolve(run),
                            new KeYBridge.Settings(
                                    KeYBridge.Mode.AUTO, strategyProperties, partialProofStrategyProperties));
                },
                args.length == 3 ? args[2] : null, // only verify the method "<feature>::<name>", useful for debugging
                Integer.parseInt(args[1]) // number of repetitions for evaluation purposes
        );
        String arg = args[0];
        if (arg.equals("feature"))
            shell.verify(new VerificationStrategy.FeatureBased(proofGraph));
        if (arg.equals("product"))
            shell.verify(new VerificationStrategy.OptimizedProductBased(proofGraph));
        if (arg.equals("feature-product"))
            shell.verify(new VerificationStrategy.FeatureProductBased(proofGraph));
        if (arg.equals("feature-family"))
            shell.verify(new VerificationStrategy.BestFeatureFamilyBased(proofGraph));
        VerificationStrategy.FeatureFamilyBased verificationStrategy =
                new VerificationStrategy.FeatureFamilyBased(proofGraph);
        if (arg.equals("feature-family-all"))
            while (verificationStrategy.hasNext()) {
                shell.verify(verificationStrategy);
                verificationStrategy.increment();
            }
        if (arg.equals("family"))
            shell.verify(new VerificationStrategy.FamilyBased(Paths.get("caseStudy/IntListMetaProduct")));
    }

    abstract static class VerificationStrategy {
        Core.ProofGraph proofGraph;

        VerificationStrategy(Core.ProofGraph proofGraph) {
            this.proofGraph = proofGraph;
        }

        abstract Core.ProofPlan proofPlan();

        @Override
        public String toString() {
            return getClass().getSimpleName();
        }

        // all proof plans are correctness-equivalent, so we can choose any (some may perform better than others)
        static class ChooseAny extends VerificationStrategy {
            ChooseAny(Core.ProofGraph proofGraph) {
                super(proofGraph);
            }

            @Override
            Core.ProofPlan proofPlan() {
                return new Core.ProofPlanGenerator(proofGraph).iterator().next();
            }
        }

        // feature-based strategy: no proof reuse, no feature interactions, only meaningful for methods without calls
        static class FeatureBased extends VerificationStrategy {
            FeatureBased(Core.ProofGraph proofGraph) {
                super(proofGraph);
            }

            @Override
            Core.ProofPlan proofPlan() {
                Core.ProofPlan proofPlan = new ChooseAny(proofGraph).proofPlan();
                proofPlan.nodes = proofPlan.nodes.stream()
                        .filter(node -> node.bindings.isEmpty())
                        .collect(Collectors.toSet());
                proofPlan.edges = new HashSet<>();
                return proofPlan;
            }
        }

        // optimized product-based strategy: no proof reuse, only optimized by eliminating duplicate proofs
        static class OptimizedProductBased extends VerificationStrategy {
            OptimizedProductBased(Core.ProofGraph proofGraph) {
                super(proofGraph);
            }

            @Override
            Core.ProofPlan proofPlan() {
                Core.ProofPlan proofPlan = new ChooseAny(proofGraph).proofPlan();
                proofPlan.nodes = proofPlan.nodes.stream()
                        .filter(Core.Node::isComplete)
                        .collect(Collectors.toSet());
                proofPlan.edges = new HashSet<>();
                return proofPlan;
            }
        }

        // feature-product-based strategy: slight proof reuse by one phase of partial proofs
        static class FeatureProductBased extends VerificationStrategy {
            FeatureProductBased(Core.ProofGraph proofGraph) {
                super(proofGraph);
            }

            @Override
            Core.ProofPlan proofPlan() {
                Core.ProofPlan proofPlan = new ChooseAny(proofGraph).proofPlan();
                proofPlan.nodes = proofPlan.nodes.stream()
                        .filter(node -> node.bindings.isEmpty() || node.isComplete())
                        .collect(Collectors.toSet());
                proofPlan.edges = proofPlan.nodes.stream()
                        .flatMap(targetNode -> proofPlan.nodes.stream()
                                .filter(sourceNode -> targetNode.method.equals(sourceNode.method) &&
                                        targetNode.bindings.containsAll(sourceNode.bindings) &&
                                        targetNode.bindings.size() > sourceNode.bindings.size())
                                .map(sourceNode -> new Core.Edge(sourceNode, targetNode))).collect(Collectors.toSet());
                return proofPlan;
            }
        }

        // feature-family-based strategy: several partial proof phases to improve proof reuse
        static class FeatureFamilyBased extends VerificationStrategy {
            List<Core.ProofPlan> optimizedProofPlans;
            int i = 0;

            FeatureFamilyBased(Core.ProofGraph proofGraph) {
                super(proofGraph);
                optimizedProofPlans = new ArrayList<>(
                        Core.ProofPlanGenerator.allOptimizedProofPlans(proofGraph));
            }

            @Override
            Core.ProofPlan proofPlan() {
                return i < optimizedProofPlans.size() ? optimizedProofPlans.get(i) : null;
            }

            void increment() {
                i++;
            }

            boolean hasNext() {
                return i < optimizedProofPlans.size();
            }

            @Override
            public String toString() {
                return super.toString() + "-" + BestFeatureFamilyBased.score(proofPlan());
            }
        }

        // heuristic for proof plan with maximal proof reuse
        static class BestFeatureFamilyBased extends VerificationStrategy {
            BestFeatureFamilyBased(Core.ProofGraph proofGraph) {
                super(proofGraph);
            }

            static int score(Core.ProofPlan proofPlan) {
                return proofPlan.edges.stream()
                        .map(edge -> edge.newBindings().size()).mapToInt(Integer::intValue).sum();
            }

            @Override
            Core.ProofPlan proofPlan() {
                HashMap<Core.ProofPlan, Integer> scores = new HashMap<>();
                Set<Core.ProofPlan> optimizedProofPlans =
                        Core.ProofPlanGenerator.allOptimizedProofPlans(proofGraph);
                for (Core.ProofPlan proofPlan : optimizedProofPlans)
                    scores.put(proofPlan, score(proofPlan));
                //noinspection ConstantConditions
                return scores.entrySet().stream().min(Map.Entry.comparingByValue()).orElse(null).getKey();
            }
        }

        // family-based can be evaluated using a meta-product - this is just a dummy class
        static class FamilyBased extends VerificationStrategy {
            Path path;

            public FamilyBased(Path path) {
                super(null);
                this.path = path;
            }

            @Override
            Core.ProofPlan proofPlan() {
                return null;
            }
        }
    }
}
