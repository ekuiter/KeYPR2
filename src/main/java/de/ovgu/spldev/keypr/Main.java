package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.strategy.StrategyProperties;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args) {
        Utils.deleteDirectory(Paths.get("caseStudy/proofRepository"));
        Core.VerificationGraph verificationGraph = // path to FeatureIDE project that should be verified
                Shell.getSoftwareProductLine(Paths.get("caseStudy/IntList")).verificationGraph();
        Shell shell = new Shell(
                verificationGraph,
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
                            Paths.get("caseStudy/proofRepository").resolve(run),
                            new KeYBridge.Settings(
                                    KeYBridge.Mode.AUTO, strategyProperties, partialProofStrategyProperties));
                },
                null, // only verify the method "<feature>::<name>", useful for debugging
                1  // number of repetitions for evaluation purposes
        );
        shell.verify(new VerificationStrategy.FeatureBased(verificationGraph));
        shell.verify(new VerificationStrategy.OptimizedProductBased(verificationGraph));
        shell.verify(new VerificationStrategy.FeatureProductBased(verificationGraph));
        shell.verify(new VerificationStrategy.BestFeatureFamilyBased(verificationGraph));
        shell.verify(new VerificationStrategy.FeatureFamilyBased(verificationGraph));
        shell.verify(new VerificationStrategy.FamilyBased(Paths.get("caseStudy/IntListMetaProduct")));
    }

    abstract static class VerificationStrategy {
        Core.VerificationGraph verificationGraph;

        VerificationStrategy(Core.VerificationGraph verificationGraph) {
            this.verificationGraph = verificationGraph;
        }

        abstract Core.VerificationPlan verificationPlan();

        // all verification plans are correctness-equivalent, so we can choose any (some may perform better than others)
        static class ChooseAny extends VerificationStrategy {
            ChooseAny(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                return new Core.VerificationPlanGenerator(verificationGraph).iterator().next();
            }
        }

        // feature-based strategy: no proof reuse, no feature interactions, only meaningful for methods without calls
        static class FeatureBased extends VerificationStrategy {
            FeatureBased(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                Core.VerificationPlan verificationPlan = new ChooseAny(verificationGraph).verificationPlan();
                verificationPlan.nodes = verificationPlan.nodes.stream()
                        .filter(node -> node.bindings.isEmpty())
                        .collect(Collectors.toSet());
                verificationPlan.edges = new HashSet<>();
                return verificationPlan;
            }
        }

        // optimized product-based strategy: no proof reuse, only optimized by eliminating duplicate proofs
        static class OptimizedProductBased extends VerificationStrategy {
            OptimizedProductBased(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                Core.VerificationPlan verificationPlan = new ChooseAny(verificationGraph).verificationPlan();
                verificationPlan.nodes = verificationPlan.nodes.stream()
                        .filter(Core.Node::isComplete)
                        .collect(Collectors.toSet());
                verificationPlan.edges = new HashSet<>();
                return verificationPlan;
            }
        }

        // feature-product-based strategy: slight proof reuse by one phase of partial proofs
        static class FeatureProductBased extends VerificationStrategy {
            FeatureProductBased(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                Core.VerificationPlan verificationPlan = new ChooseAny(verificationGraph).verificationPlan();
                verificationPlan.nodes = verificationPlan.nodes.stream()
                        .filter(node -> node.bindings.isEmpty() || node.isComplete())
                        .collect(Collectors.toSet());
                verificationPlan.edges = verificationPlan.nodes.stream()
                        .flatMap(targetNode -> verificationPlan.nodes.stream()
                                .filter(sourceNode -> targetNode.method.equals(sourceNode.method) &&
                                        targetNode.bindings.containsAll(sourceNode.bindings) &&
                                        targetNode.bindings.size() > sourceNode.bindings.size())
                                .map(sourceNode -> new Core.Edge(sourceNode, targetNode))).collect(Collectors.toSet());
                return verificationPlan;
            }
        }

        // feature-family-based strategy: several partial proof phases to improve proof reuse
        static class FeatureFamilyBased extends VerificationStrategy {
            List<Core.VerificationPlan> optimizedVerificationPlans;
            int i = 0;

            FeatureFamilyBased(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
                optimizedVerificationPlans = new ArrayList<>(
                        Core.VerificationPlanGenerator.allOptimizedVerificationPlans(verificationGraph));
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                return i < optimizedVerificationPlans.size() ? optimizedVerificationPlans.get(i) : null;
            }

            void increment() {
                i++;
            }
        }

        // heuristic for verification plan with maximal proof reuse
        static class BestFeatureFamilyBased extends VerificationStrategy {
            BestFeatureFamilyBased(Core.VerificationGraph verificationGraph) {
                super(verificationGraph);
            }

            @Override
            Core.VerificationPlan verificationPlan() {
                HashMap<Core.VerificationPlan, Integer> scores = new HashMap<>();
                Set<Core.VerificationPlan> optimizedVerificationPlans =
                        Core.VerificationPlanGenerator.allOptimizedVerificationPlans(verificationGraph);
                for (Core.VerificationPlan verificationPlan : optimizedVerificationPlans)
                    scores.put(verificationPlan, verificationPlan.edges.stream()
                            .map(edge -> edge.newBindings().size()).mapToInt(Integer::intValue).sum());
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
            Core.VerificationPlan verificationPlan() {
                return null;
            }
        }
    }
}
