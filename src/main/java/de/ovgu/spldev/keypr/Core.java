package de.ovgu.spldev.keypr;

import de.uka.ilkd.key.proof.Proof;

import java.io.File;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class Core {
    public static class Signature {
        static final Pattern PATTERN = Pattern.compile("^(.*)\\s+(.*)\\((.*)\\)$");

        String type;
        String name;
        List<Utils.Pair<String, String>> parameters;

        Signature(String type, String name, List<Utils.Pair<String, String>> parameters) {
            this.type = type;
            this.name = name;
            this.parameters = parameters;
        }

        Signature(String spec) {
            Matcher matcher = PATTERN.matcher(spec.trim());
            if (!matcher.find())
                throw new IllegalArgumentException(
                        "invalid function specification " + spec + ", expected <type> <name>(<parameters>)");
            type = matcher.group(1).trim();
            name = matcher.group(2).trim();
            parameters = new ArrayList<>();
            AtomicInteger paramCounter = new AtomicInteger(1);
            Arrays.stream(matcher.group(3).trim().split(","))
                    .map(String::trim)
                    .map(str -> str.split("\\s+"))
                    .forEach(_parts -> {
                        if (String.join("", _parts).isEmpty())
                            return;
                        if (_parts.length == 1) {
                            parameters.add(new Utils.Pair<>(_parts[0], "_" + paramCounter));
                            paramCounter.getAndIncrement();
                        } else if (_parts.length == 2)
                            parameters.add(new Utils.Pair<>(_parts[0], _parts[1]));
                        else
                            throw new IllegalArgumentException("invalid parameters in signature specification");
                    });
        }

        Signature copy() {
            return new Signature(type, name, new ArrayList<>(parameters));
        }

        Signature withType(String type) {
            Signature thisCopy = copy();
            thisCopy.type = type;
            return thisCopy;
        }

        Signature withName(String name) {
            Signature thisCopy = copy();
            thisCopy.name = name;
            return thisCopy;
        }

        Signature prependName(String name) {
            return withName(name + this.name);
        }

        Signature appendName(String name) {
            return withName(this.name + name);
        }

        Signature appendParameter(String type, String name) {
            Signature thisCopy = copy();
            thisCopy.parameters = new ArrayList<>(this.parameters);
            thisCopy.parameters.add(new Utils.Pair<>(type, name));
            return thisCopy;
        }

        String parametersToJavaString() {
            return parameters != null ? "(" + parameters.stream()
                    .map(entry -> entry.first + (entry.second != null ? " " + entry.second : ""))
                    .collect(Collectors.joining(", ")) + ")" : "";
        }

        String parametersToArgumentString() {
            return parameters != null ? "(" + parameters.stream()
                    .map(entry -> entry.second)
                    .collect(Collectors.joining(", ")) + ")" : "";
        }

        String toCallString() {
            return name + parametersToArgumentString();
        }

        public String toString() {
            return type + " " + name + parametersToJavaString();
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Signature signature = (Signature) o;
            return Objects.equals(type, signature.type) && Objects.equals(name, signature.name) &&
                    Objects.equals(parameters, signature.parameters);
        }

        @Override
        public int hashCode() {
            return Objects.hash(type, name, parameters);
        }
    }

    public static class HoareTriple {
        String requires;
        String implementation;
        String ensures;
        String assignable;
        Signature signature;
        Set<Signature> signatures;
        Set<String> implementationCalls;
        Set<String> contractCalls;

        HoareTriple(String requires, String code, String ensures, String assignable,
                    Set<String> signatures, Set<String> implementationCalls, Set<String> contractCalls) {
            String[] parts = code.split("\\{", 2);
            this.requires = requires;
            this.implementation = "{\n    " + parts[1].trim();
            this.ensures = ensures;
            this.assignable = assignable;
            this.signature = new Signature(parts[0].trim());
            this.signatures = signatures.stream().map(Signature::new).collect(Collectors.toSet());
            this.implementationCalls = implementationCalls;
            this.contractCalls = contractCalls;
        }

        Set<String> implementationCalls() {
            return implementationCalls;
        }

        Set<String> contractCalls() {
            return contractCalls;
        }
    }

    public static class Method {
        String feature;
        String name;
        HoareTriple hoareTriple;

        Method(String feature, String name, HoareTriple hoareTriple) {
            this.feature = feature;
            this.name = name;
            this.hoareTriple = hoareTriple;
        }

        @Override
        public String toString() {
            return String.format("%s::%s", feature, name);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Method method = (Method) o;
            return feature.equals(method.feature) && name.equals(method.name);
        }

        @Override
        public int hashCode() {
            return Objects.hash(feature, name);
        }

        Set<Call> implementationCalls() {
            return hoareTriple.implementationCalls().stream()
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
        }

        Set<Call> contractCalls() {
            return hoareTriple.contractCalls().stream()
                    .map(call -> new Call(this, call))
                    .collect(Collectors.toSet());
        }

        Set<Call> calls() {
            Set<Call> calls = new HashSet<>(implementationCalls());
            calls.addAll(contractCalls());
            return calls;
        }

        Set<Call> extendedCalls(Set<Binding> bindings, int i) {
            if (bindings.isEmpty())
                return i == 0 ? calls() : contractCalls();
            else {
                Binding binding = bindings.iterator().next();
                Set<Binding> smallerBindings = new HashSet<>(bindings);
                smallerBindings.remove(binding);
                Set<Call> extendedCalls = new HashSet<>(extendedCalls(smallerBindings, i));
                if (extendedCalls.contains(binding.source))
                    extendedCalls.addAll(binding.destination.extendedCalls(smallerBindings, i + 1));
                return extendedCalls;
            }
        }

        Set<Call> extendedCalls(Set<Binding> bindings) {
            return extendedCalls(bindings, 0);
        }
    }

    public static class Call {
        Method in;
        String to;

        Call(Method in, String to) {
            this.in = in;
            this.to = to;
        }

        @Override
        public String toString() {
            return String.format("%s.%s", in, to);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Call call = (Call) o;
            return in.equals(call.in) && to.equals(call.to);
        }

        @Override
        public int hashCode() {
            return Objects.hash(in, to);
        }
    }

    public static class Binding {
        Call source;
        Method destination;

        Binding(Call source, Method destination) {
            this.source = source;
            this.destination = destination;
        }

        @Override
        public String toString() {
            return String.format("%s -> %s", source, destination);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Binding binding = (Binding) o;
            return source.equals(binding.source) && destination.equals(binding.destination);
        }

        @Override
        public int hashCode() {
            return Objects.hash(source, destination);
        }
    }

    public static class SoftwareProductLine {
        List<String> features;
        Set<Set<String>> configurations;
        Set<Method> methods;

        SoftwareProductLine(List<String> features, Set<Set<String>> configurations, Set<Method> methods) {
            this.features = features;
            this.configurations = new HashSet<>(configurations);
            this.methods = new HashSet<>(methods);
        }

        Comparator<String> featureOrder() {
            return Comparator.comparing(feature -> IntStream.range(0, features.size())
                    .filter(i -> feature.equals(features.get(i))).findFirst().orElse(-1));
        }

        Set<Call> calls() {
            return methods.stream().flatMap(method -> method.calls().stream()).collect(Collectors.toSet());
        }

        boolean hasMethod(String feature, String name) {
            return methods.stream().anyMatch(method -> method.feature.equals(feature) && method.name.equals(name));
        }

        Set<String> restrictConfiguration(Set<String> configuration, String name) {
            return configuration.stream().filter(feature -> hasMethod(feature, name)).collect(Collectors.toSet());
        }

        List<String> orderedConfiguration(Set<String> configuration) {
            List<String> orderedConfiguration = new ArrayList<>(configuration);
            orderedConfiguration.sort(featureOrder());
            return orderedConfiguration;
        }

        boolean isLastFeature(Set<String> configuration, String feature, String method) {
            List<String> orderedConfiguration = orderedConfiguration(restrictConfiguration(configuration, method));
            return !orderedConfiguration.isEmpty() &&
                    orderedConfiguration.get(orderedConfiguration.size() - 1).equals(feature);
        }

        boolean isBeforeFeature(Set<String> configuration, String featureA, String featureB, String method) {
            List<String> orderedConfiguration = orderedConfiguration(restrictConfiguration(configuration, method));
            for (int i = 0; i < orderedConfiguration.size() - 1; i++)
                if (orderedConfiguration.get(i).equals(featureA))
                    return orderedConfiguration.get(i + 1).equals(featureB);
            return false;
        }

        Set<Method> derivedMethods(Set<String> configuration) {
            Set<Method> derivedMethods = methods.stream()
                    .filter(method -> isLastFeature(configuration, method.feature, method.name))
                    .collect(Collectors.toSet());
            boolean done = false;
            while (!done) {
                Set<Method> newDerivedMethods = derivedMethods.stream()
                        .flatMap(method -> methods.stream().filter(_method ->
                                _method.name.equals(method.name) &&
                                        method.implementationCalls().contains(new Call(method, "original")) &&
                                        isBeforeFeature(configuration, _method.feature, method.feature, method.name)))
                        .collect(Collectors.toSet());
                newDerivedMethods.removeAll(derivedMethods);
                derivedMethods.addAll(newDerivedMethods);
                done = newDerivedMethods.isEmpty();
            }
            return derivedMethods;
        }

        Set<Binding> derivedBindings(Set<String> configuration) {
            return calls().stream().flatMap(call -> {
                if (call.to.equals("original"))
                    return methods.stream().filter(method -> method.name.equals(call.in.name) &&
                            isBeforeFeature(configuration, method.feature, call.in.feature, method.name))
                            .map(method -> new Binding(call, method));
                else
                    return methods.stream().filter(method -> method.name.equals(call.to) &&
                            isLastFeature(configuration, method.feature, method.name))
                            .map(method -> new Binding(call, method));
            }).collect(Collectors.toSet());
        }

        @SuppressWarnings("unused")
        VerificationGraph verificationGraph() {
            return VerificationGraph.forSoftwareProductLine(this);
        }
    }

    public static class Node {
        static int idCounter = 0;
        int id;
        Method method;
        Set<Binding> bindings;

        Node(Method method, Set<Binding> bindings) {
            this.id = idCounter++;
            this.method = method;
            this.bindings = new HashSet<>(bindings);
        }

        @Override
        public String toString() {
            return String.format("%s[%d]", method, bindings.size());
        }

        String toShortString() {
            return String.format("%d", bindings.size());
        }

        String toLongString() {
            return String.format("%s%s", method, bindings);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Node node = (Node) o;
            return method.equals(node.method) && bindings.equals(node.bindings);
        }

        @Override
        public int hashCode() {
            return Objects.hash(method, bindings);
        }

        Set<Call> unboundCalls() {
            Set<Call> unboundCalls = new HashSet<>(method.extendedCalls(bindings));
            unboundCalls.removeAll(bindings.stream().map(binding -> binding.source).collect(Collectors.toSet()));
            return unboundCalls;
        }

        boolean isComplete() {
            return unboundCalls().isEmpty();
        }
    }

    public static class Edge {
        Node sourceNode;
        Node targetNode;

        Edge(Node sourceNode, Node targetNode) {
            this.sourceNode = sourceNode;
            this.targetNode = targetNode;
        }

        Set<Binding> newBindings() {
            return targetNode.bindings.stream()
                    .filter(binding -> !sourceNode.bindings.contains(binding))
                    .collect(Collectors.toSet());
        }

        @Override
        public String toString() {
            return String.format("%s -%s-> %s", sourceNode, newBindings(), targetNode);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            Edge edge = (Edge) o;
            return sourceNode.equals(edge.sourceNode) && targetNode.equals(edge.targetNode);
        }

        @Override
        public int hashCode() {
            return Objects.hash(sourceNode, targetNode);
        }
    }

    public static class VerificationGraph {
        Set<Node> nodes;
        Set<Edge> edges;
        HashMap<Node, Integer> completeNodeOccurrences;

        // Algorithm 1: Verification Graph for an SPL
        static VerificationGraph forSoftwareProductLine(SoftwareProductLine spl) {
            Comparator<String> featureOrder = spl.featureOrder();
            Set<Node> nodes = spl.methods.stream() // line 1
                    .map(method -> new Node(method, new HashSet<>()))
                    .collect(Collectors.toSet());
            List<Binding> bindings = spl.configurations.stream() // line 2
                    .flatMap(configuration -> spl.derivedBindings(configuration).stream())
                    .sorted((b1, b2) -> featureOrder.compare(b2.destination.feature, b1.destination.feature)) // line 3
                    .collect(Collectors.toList());
            for (Binding binding : bindings) // line 4
                nodes.addAll(nodes.stream() // line 5
                        .filter(node -> node.unboundCalls().contains(binding.source))
                        .map(node -> {
                            Set<Binding> _bindings = new HashSet<>(node.bindings);
                            _bindings.add(binding);
                            return new Node(node.method, _bindings);
                        }).collect(Collectors.toSet()));
            nodes.removeAll(nodes.stream().filter(node -> spl.configurations.stream() // line 6
                    .noneMatch(configuration ->
                            spl.derivedMethods(configuration).contains(node.method) &&
                                    spl.derivedBindings(configuration).containsAll(node.bindings)))
                    .collect(Collectors.toSet()));
            Set<Edge> edges = nodes.stream().flatMap(targetNode -> nodes.stream() // line 7
                    .filter(sourceNode -> targetNode.method.equals(sourceNode.method) &&
                            targetNode.bindings.containsAll(sourceNode.bindings) &&
                            targetNode.bindings.size() == sourceNode.bindings.size() + 1)
                    .map(sourceNode -> new Edge(sourceNode, targetNode))).collect(Collectors.toSet());
            HashMap<Node, Integer> completeNodeOccurrences = new HashMap<>();
            nodes.stream().filter(Node::isComplete).forEach(node -> completeNodeOccurrences.put(node,
                    (int) spl.configurations.stream().filter(configuration ->
                            spl.derivedMethods(configuration).contains(node.method) &&
                                    spl.derivedBindings(configuration).containsAll(node.bindings))
                            .count()));
            return new VerificationGraph(nodes, edges, completeNodeOccurrences); // line 8
        }

        VerificationGraph(Set<Node> nodes, Set<Edge> edges, HashMap<Node, Integer> completeNodeOccurrences) {
            this.nodes = new HashSet<>(nodes);
            this.edges = new HashSet<>(edges);
            this.completeNodeOccurrences = new HashMap<>(completeNodeOccurrences);
        }

        String toDot() {
            return String.format("digraph {\n" +
                            "rankdir = LR;\n" +
                            "%s\n" +
                            "%s\n" +
                            "}",
                    nodes.stream().map(node -> node.method).distinct().map(method ->
                            String.format("subgraph \"cluster_%s\" {\n" +
                                            "label = \"%s\";\n" +
                                            "%s\n" +
                                            "}\n",
                                    method,
                                    method,
                                    nodes.stream()
                                            .filter(node -> node.method.equals(method))
                                            .map(node -> String.format(
                                                    "\"%s\" [label = \"%s\", tooltip = \"%s\", style = \"%s\"];",
                                                    node.id, node.toShortString(), node.toLongString(),
                                                    node.isComplete() ? "diagonals" : "solid"))
                                            .collect(Collectors.joining("\n"))))
                            .collect(Collectors.joining("\n")),
                    edges.stream().map(edge -> String.format("\"%s\" -> \"%s\" [tooltip = \"%s\"];",
                            edge.sourceNode.id, edge.targetNode.id, edge.newBindings()))
                            .collect(Collectors.joining("\n")));
        }
    }

    public static class VerificationPlan {
        Set<Node> nodes;
        Set<Edge> edges;

        VerificationPlan(Set<Node> nodes, Set<Edge> edges) {
            this.nodes = new HashSet<>(nodes);
            this.edges = new HashSet<>(edges);
        }

        String toDot() {
            return new VerificationGraph(nodes, edges, new HashMap<>()).toDot();
        }

        VerificationPlan removeDeadEnds() {
            VerificationPlan verificationPlan = new VerificationPlan(nodes, edges);
            boolean done = false;
            while (!done) {
                Set<Node> removeNodes = verificationPlan.nodes.stream()
                        .filter(node -> verificationPlan.edges.stream().noneMatch(edge -> edge.sourceNode.equals(node)))
                        .filter(node -> !node.isComplete())
                        .collect(Collectors.toSet());
                verificationPlan.edges.removeAll(verificationPlan.edges.stream()
                        .filter(edge -> removeNodes.stream().anyMatch(node -> edge.targetNode.equals(node)))
                        .collect(Collectors.toSet()));
                verificationPlan.nodes.removeAll(removeNodes);
                done = removeNodes.isEmpty();
            }
            return verificationPlan;
        }

        VerificationPlan combineLinearSubPaths() {
            VerificationPlan verificationPlan = new VerificationPlan(nodes, edges);
            boolean done = false;
            while (!done) {
                Node removeNode = verificationPlan.nodes.stream()
                        .filter(node -> verificationPlan.edges.stream()
                                .filter(edge -> edge.sourceNode.equals(node)).count() == 1)
                        .findAny().orElse(null);
                if (removeNode != null) {
                    Edge parentEdge = verificationPlan.edges.stream().filter(edge -> edge.targetNode.equals(removeNode))
                            .findFirst().orElse(null);
                    @SuppressWarnings("OptionalGetWithoutIsPresent") Edge childEdge =
                            verificationPlan.edges.stream().filter(edge -> edge.sourceNode.equals(removeNode))
                                    .findFirst().get();
                    if (parentEdge != null) {
                        verificationPlan.edges.add(new Edge(parentEdge.sourceNode, childEdge.targetNode));
                        verificationPlan.edges.remove(parentEdge);
                    }
                    verificationPlan.edges.remove(childEdge);
                    verificationPlan.nodes.remove(removeNode);
                } else
                    done = true;
            }
            return verificationPlan;
        }

        VerificationAttempt verificationAttempt(VerificationSystem verificationSystem) {
            return new VerificationAttempt(this, verificationSystem);
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            VerificationPlan that = (VerificationPlan) o;
            return nodes.equals(that.nodes) && edges.equals(that.edges);
        }

        @Override
        public int hashCode() {
            return Objects.hash(nodes, edges);
        }
    }

    public static class VerificationPlanGenerator implements Iterable<VerificationPlan> {
        VerificationGraph verificationGraph;
        List<List<Edge>> edgeFamily;

        VerificationPlanGenerator(VerificationGraph verificationGraph) {
            this.verificationGraph = verificationGraph;
            edgeFamily = verificationGraph.nodes.stream()
                    .map(node -> verificationGraph.edges.stream().filter(edge -> edge.targetNode.equals(node))
                            .collect(Collectors.toList()))
                    .filter(edges -> !edges.isEmpty()).collect(Collectors.toList());
        }

        @SuppressWarnings("NullableProblems")
        @Override
        public Iterator<VerificationPlan> iterator() {
            return new Iterator<VerificationPlan>() {
                final int[] indices = new int[edgeFamily.size()];
                boolean done = false;

                void increment() {
                    if (indices.length == 0) {
                        done = true;
                        return;
                    }
                    int i = 0;
                    indices[i]++;
                    while (indices[i] >= edgeFamily.get(i).size()) {
                        indices[i] = 0;
                        i++;
                        if (i >= indices.length) {
                            done = true;
                            return;
                        }
                        indices[i]++;
                    }
                }

                @Override
                public boolean hasNext() {
                    return !done;
                }

                @Override
                public VerificationPlan next() {
                    Set<Edge> edges = new HashSet<>();
                    for (int i = 0; i < indices.length; i++) {
                        edges.add(edgeFamily.get(i).get(indices[i]));
                    }
                    increment();
                    return new VerificationPlan(verificationGraph.nodes, edges);
                }
            };
        }

        static Set<Core.VerificationPlan> allOptimizedVerificationPlans(VerificationGraph verificationGraph) {
            Set<Core.VerificationPlan> optimizedVerificationPlans = new HashSet<>();
            for (Core.VerificationPlan verificationPlan : new Core.VerificationPlanGenerator(verificationGraph))
                optimizedVerificationPlans.add(verificationPlan.removeDeadEnds().combineLinearSubPaths());
            return optimizedVerificationPlans;
        }
    }

    public static class JavaClassGenerator {
        Core.State state;

        JavaClassGenerator(Core.State state) {
            this.state = state;
        }

        String generateContract(String... args) {
            if (args.length % 2 != 0)
                throw new IllegalArgumentException("expected map of JML keywords to values");
            StringBuilder sb = new StringBuilder();
            sb.append("/*@ ");
            for (int i = 0; i < args.length; i += 2)
                sb.append(i > 0 ? "\n  @ " : "").append(args[i]).append(" ").append(args[i + 1]);
            return sb.append(" */").toString();
        }

        Core.Signature originalSignature(Core.Method method) {
            return method.hoareTriple.signature.withName(method.feature + "_" + method.name + "_original");
        }

        Core.Signature scopedSignature(Core.Method method, Core.Signature signature) {
            return signature.prependName(method.feature + "_" + method.name + "_");
        }

        String replaceOriginal(String condition, boolean isRequires, Core.Signature signature) {
            return condition.replace("\\original",
                    (isRequires || signature.type.equals("void") ? signature :
                            signature.appendParameter(signature.type,
                                    signature.equals(originalSignature(state.method)) ? "\\result" : "res"))
                            .appendName(isRequires ? "_requires" : "_ensures")
                            .toCallString());
        }

        String getLocSet(String assignable) {
            return assignable.equals("\\everything")
                    ? "\\set_minus(\\everything, \\nothing)"
                    : assignable.equals("\\nothing")
                    ? "\\set_minus(\\nothing, \\everything)"
                    : assignable;
        }

        String generateAbstractMethod(Core.Method callingMethod, Core.Signature signature) {
            Core.Signature requiresSignature =
                    scopedSignature(callingMethod, signature).withType("boolean").appendName("_requires");
            Function<String, Core.Signature> ensuresSignature =
                    res -> scopedSignature(callingMethod,
                            signature.type.equals("void")
                                    ? signature
                                    : signature.appendParameter(signature.type, res))
                            .withType("boolean").appendName("_ensures");
            Core.Signature assignableSignature =
                    scopedSignature(callingMethod, signature).withType("\\locset").appendName("_assignable");
            Optional<Core.Binding> binding = state.bindings.stream()
                    .filter(_binding -> _binding.source.in.equals(callingMethod) &&
                            _binding.source.to.equals(signature.name))
                    .findFirst();
            String requiresExpansion = binding
                    .map(_binding -> " { return " + replaceOriginal(
                            _binding.destination.hoareTriple.requires,
                            true, originalSignature(_binding.destination)) + "; }")
                    .orElse(";");
            String ensuresExpansion = binding
                    .map(_binding -> " { return " + replaceOriginal(
                            _binding.destination.hoareTriple.ensures
                                    .replace("\\result", "res"),
                            false, originalSignature(_binding.destination)) + "; }")
                    .orElse(";");
            String assignableExpansion = binding
                    .map(_binding -> " { return " +
                            getLocSet(_binding.destination.hoareTriple.assignable) + "; }")
                    .orElse(";");
            return String.format("%s\n%s%s%s",
                    binding.filter(_binding -> !_binding.destination.contractCalls().isEmpty())
                            .map(_binding -> generateAbstractMethod(_binding.destination,
                                    _binding.destination.hoareTriple
                                            .signature.withName("original")) + "\n").orElse(""),
                    generateContract(
                            "model", requiresSignature + requiresExpansion,
                            "model", ensuresSignature.apply("res") + ensuresExpansion,
                            "model", assignableSignature + assignableExpansion),
                    callingMethod.equals(state.method) ? "\n" +
                            generateContract("requires", requiresSignature.toCallString() + ";",
                                    "ensures", ensuresSignature.apply("\\result").toCallString() + ";",
                                    "assignable", assignableSignature.toCallString() + ";") : "",
                    callingMethod.equals(state.method) ? String.format("\n%s;", signature.toString()) : "");
        }

        String generate() {
            Core.HoareTriple hoareTriple = state.method.hoareTriple;
            return String.format("class Gen {%s\n\n%s\n%s %s\n}",
                    hoareTriple.signatures.stream()
                            .map(signature -> generateAbstractMethod(state.method, signature))
                            .collect(Collectors.joining("\n")),
                    generateContract(
                            "requires", replaceOriginal(
                                    hoareTriple.requires, true, originalSignature(state.method)) + ";",
                            "ensures", replaceOriginal(
                                    hoareTriple.ensures, false, originalSignature(state.method)) + ";",
                            "assignable", hoareTriple.assignable + ";").trim(),
                    hoareTriple.signature.withName("main"),
                    hoareTriple.implementation);
        }
    }

    public static class State {
        private final VerificationSystem verificationSystem;
        Method method;
        Set<Binding> bindings;
        String partialProofBefore;
        String partialProofAfter;
        Boolean isClosed;
        List<Integer> statistics;

        State(VerificationSystem verificationSystem, Method method, Set<Binding> bindings, String partialProofBefore) {
            this.verificationSystem = verificationSystem;
            this.method = method;
            this.bindings = bindings;
            this.partialProofBefore = partialProofBefore;
            verify();
        }

        @Override
        public String toString() {
            String str = method.feature + "_" + method.name + "_" + bindings.stream()
                    .map(binding -> String.format("%s_%s_%s_%s_%s",
                            binding.source.in.feature, binding.source.in.name, binding.source.to,
                            binding.destination.feature, binding.destination.name))
                    .collect(Collectors.joining("_"));
            return str.substring(0, Math.min(str.length(), 80)) + "_" + hashCode();
        }

        List<Integer> getStatistics() {
            return statistics;
        }

        File createProofContext() {
            Path proofContextPath = verificationSystem.proofRepositoryPath.resolve(toString());
            Utils.createDirectory(proofContextPath);
            Path javaClassPath = proofContextPath.resolve("Gen.java");
            Utils.writeFile(javaClassPath, new JavaClassGenerator(this).generate());
            if (partialProofBefore != null)
                Utils.writeFile(proofContextPath.resolve("problem.key"), partialProofBefore);
            return proofContextPath.toFile();
        }

        void writeProof(Proof proof) {
            partialProofAfter = KeYBridge.serializeProof(proof);
            isClosed = proof.closed();
            Path proofContextPath = verificationSystem.proofRepositoryPath.resolve(toString());
            Utils.writeFile(proofContextPath.resolve("proof.key"), partialProofAfter);
            Utils.writeFile(proofContextPath.resolve("statistics.txt"),
                    (proof.closed() ? "closed" : proof.openGoals().size() + " open") +
                            "\n" + proof.getStatistics().toString());
            statistics = new ArrayList<>();
            statistics.add(new Node(method, bindings).isComplete() ? proof.openGoals().size() : 0);
            statistics.add(proof.getStatistics().nodes);
            statistics.add(proof.getStatistics().branches);
            statistics.add(proof.getStatistics().symbExApps);
            statistics.add((int) proof.getStatistics().autoModeTimeInMillis);
        }

        void verify() {
            File proofContext = createProofContext();
            boolean isComplete = new Node(method, bindings).isComplete();
            Proof proof = KeYBridge.proveContract(
                    partialProofBefore != null
                            ? proofContext.toPath().resolve("problem.key").toFile()
                            : proofContext, verificationSystem.settings, "main",
                    isComplete, !isComplete);
            writeProof(proof);
        }
    }

    public static class VerificationAttempt {
        VerificationPlan verificationPlan;
        List<Node> sortedNodes;
        VerificationSystem verificationSystem;
        Map<Node, State> map = new HashMap<>();

        VerificationAttempt(VerificationPlan verificationPlan, VerificationSystem verificationSystem) {
            this.verificationPlan = verificationPlan;
            // this is ONE topological sorting, others are possible.
            // this is not interesting if we restrict ourselves to one CPU core and no network partitions.
            this.sortedNodes = verificationPlan.nodes.stream()
                    .sorted(Comparator.comparing(node -> node.bindings.size()))
                    .collect(Collectors.toList());
            this.verificationSystem = verificationSystem;
        }

        @Override
        public String toString() {
            return sortedNodes.toString();
        }

        void verify(String focusOnMethod) {
            for (Node node : sortedNodes)
                if (focusOnMethod == null || focusOnMethod.equals(node.method.toString())) {
                    if (verificationPlan.edges.stream().noneMatch(edge -> edge.targetNode.equals(node)))
                        map.put(node, verificationSystem.beginProof(node.method, node.bindings));
                    else {
                        @SuppressWarnings("OptionalGetWithoutIsPresent") Edge edge = verificationPlan.edges.stream()
                                .filter(_edge -> _edge.targetNode.equals(node))
                                .findFirst().get();
                        map.put(node, verificationSystem.continueProof(map.get(edge.sourceNode), edge.newBindings()));
                    }
                }
        }

        Set<State> failedProofs() {
            return sortedNodes.stream()
                    .filter(Node::isComplete)
                    .map(map::get)
                    .filter(state -> state != null && !verificationSystem.completeProof(state))
                    .collect(Collectors.toSet());
        }

        HashMap<String, List<Integer>> getStatisticsMap(HashMap<Node, Integer> occurrences) {
            HashMap<String, List<Integer>> statisticsMap = new HashMap<>();
            for (Node node : sortedNodes)
                if (map.get(node) != null) {
                    List<Integer> statistics = new ArrayList<>(map.get(node).getStatistics());
                    statistics.add(occurrences.get(node) != null ? occurrences.get(node) : 0);
                    statisticsMap.put(String.format("%s_%d", node.toString(), node.hashCode()), statistics);
                }
            return statisticsMap;
        }

        static List<Integer> addStatistics(List<Integer> statistics1, List<Integer> statistics2) {
            if (statistics1 == null)
                return statistics2;
            List<Integer> statistics = new ArrayList<>(statistics1);
            statistics.set(4, statistics1.get(4) + statistics2.get(4));
            return statistics;
        }

        static HashMap<String, List<Integer>> getStatisticsMap(List<HashMap<String, List<Integer>>> statisticsMaps) {
            HashMap<String, List<Integer>> newStatisticsMap = new HashMap<>();
            for (HashMap<String, List<Integer>> statisticsMap : statisticsMaps)
                for (Map.Entry<String, List<Integer>> entry : statisticsMap.entrySet())
                    newStatisticsMap.put(entry.getKey(),
                            addStatistics(newStatisticsMap.get(entry.getKey()), entry.getValue()));
            for (String key : newStatisticsMap.keySet())
                newStatisticsMap.get(key).set(4, newStatisticsMap.get(key).get(4) / statisticsMaps.size());
            return newStatisticsMap;
        }

        boolean isCorrect() {
            return failedProofs().isEmpty();
        }
    }

    static public class VerificationSystem {
        Path proofRepositoryPath;
        KeYBridge.Settings settings;

        VerificationSystem(Path proofRepositoryPath, KeYBridge.Settings settings) {
            this.proofRepositoryPath = proofRepositoryPath;
            this.settings = settings;
            Utils.deleteDirectory(proofRepositoryPath);
            Utils.createDirectory(proofRepositoryPath);
            KeYBridge.initialize();
        }

        Core.State beginProof(Core.Method method, Set<Core.Binding> bindings) {
            return new Core.State(this, method, new HashSet<>(bindings), null);
        }

        Core.State continueProof(Core.State state, Set<Core.Binding> bindings) {
            HashSet<Core.Binding> newBindings = new HashSet<>(state.bindings);
            newBindings.addAll(bindings);
            return new Core.State(this, state.method, newBindings, state.partialProofAfter);
        }

        boolean completeProof(Core.State state) {
            return state.isClosed;
        }
    }
}
