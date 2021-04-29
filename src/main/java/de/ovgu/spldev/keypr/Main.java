package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.strategy.StrategyProperties;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

public class Main {
    public static void main(String[] args) {
        Path path = Paths.get("caseStudy/IntList"); // path to FeatureIDE project that should be verified
        // KeY parameters and target directory
        Supplier<Core.VerificationSystem> verificationSystemSupplier = () -> {
            HashMap<String, String> strategyProperties = new HashMap<>();
            strategyProperties.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
            strategyProperties.put(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
            strategyProperties.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
            HashMap<String, String> partialProofStrategyProperties = new HashMap<>();
            partialProofStrategyProperties.put(
                    StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
            return new Core.VerificationSystem(
                    Paths.get("caseStudy/proofRepository"),
                    new KeYBridge.Settings(KeYBridge.Mode.AUTO, strategyProperties, partialProofStrategyProperties));
        };
        // verification plans represent a spectrum of possible verification strategies, set null for family-based
        Function<Core.VerificationGraph, Core.VerificationPlan> strategy;
        String focusOnMethod = null; // only verify the method "<feature>::<name>", useful for debugging
        int N = 0; // number of repetitions for evaluation purposes

        strategy = Strategy::featureBased;
        // strategy = Strategy::optimizedProductBased;
        // strategy = Strategy::featureProductBased;
        strategy = Strategy::bestFeatureFamilyBased;
        // path = Paths.get("caseStudy/IntListMetaProduct");
        // strategy = null;

        Shell.verify(path, verificationSystemSupplier, strategy, focusOnMethod, N);
    }

    static class Strategy {
        // all verification plans are correctness-equivalent, so we can choose any (some may perform better than others)
        static Core.VerificationPlan chooseAny(Core.VerificationGraph verificationGraph) {
            return new Core.VerificationPlanGenerator(verificationGraph).iterator().next();
        }

        // feature-based strategy: no proof reuse, no feature interactions, only meaningful for methods without calls
        static Core.VerificationPlan featureBased(Core.VerificationGraph verificationGraph) {
            Core.VerificationPlan verificationPlan = chooseAny(verificationGraph);
            verificationPlan.nodes = verificationPlan.nodes.stream()
                    .filter(node -> node.bindings.isEmpty())
                    .collect(Collectors.toSet());
            verificationPlan.edges = new HashSet<>();
            return verificationPlan;
        }

        // optimized product-based strategy: no proof reuse, only optimized by eliminating duplicate proofs
        static Core.VerificationPlan optimizedProductBased(Core.VerificationGraph verificationGraph) {
            Core.VerificationPlan verificationPlan = chooseAny(verificationGraph);
            verificationPlan.nodes = verificationPlan.nodes.stream()
                    .filter(Core.Node::isComplete)
                    .collect(Collectors.toSet());
            verificationPlan.edges = new HashSet<>();
            return verificationPlan;
        }

        // feature-product-based strategy: slight proof reuse by one phase of partial proofs
        static Core.VerificationPlan featureProductBased(Core.VerificationGraph verificationGraph) {
            Core.VerificationPlan verificationPlan = chooseAny(verificationGraph);
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

        // feature-family-based strategy: several partial proof phases to improve proof reuse
        static Core.VerificationPlan bestFeatureFamilyBased(Core.VerificationGraph verificationGraph) {
            HashMap<Core.VerificationPlan, Integer> scores = new HashMap<>();
            Set<Core.VerificationPlan> optimizedVerificationPlans =
                    Core.VerificationPlanGenerator.allOptimizedVerificationPlans(verificationGraph);
            for (Core.VerificationPlan verificationPlan : optimizedVerificationPlans)
                scores.put(verificationPlan, verificationPlan.edges.stream()
                        .map(edge -> edge.newBindings().size()).mapToInt(Integer::intValue).sum());
            //noinspection ConstantConditions
            return scores.entrySet().stream().min(Map.Entry.comparingByValue()).orElse(null).getKey();
        }

        // unoptimized product-based can be calculated from optimized product-based and method occurrences
        // family-based can be evaluated using a meta-product
    }
}
