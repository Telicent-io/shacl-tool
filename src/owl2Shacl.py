import argparse
import sys
from pathlib import Path
from typing import Tuple
from pyshacl import validate
from rdflib import Graph, RDF, RDFS, SH, OWL, XSD
from rdflib.term import URIRef, BNode, Literal, Node
from itertools import chain

SH_CLASS = URIRef("http://www.w3.org/ns/shacl#class")
SH_OR = URIRef("http://www.w3.org/ns/shacl#or")
SH_AND = URIRef("http://www.w3.org/ns/shacl#and")


def _insert_list_item(sh_graph: Graph, ont_graph: Graph, item: Node, tgt_typ: URIRef) -> Node:
    bnode = BNode()
    rest = ont_graph.value(subject=item, predicate=RDF.rest)
    value = ont_graph.value(subject=item, predicate=RDF.first)
    sh_graph.add((item, RDF.first, bnode))
    sh_graph.add((bnode, tgt_typ, value))
    sh_graph.add((item, RDF.rest, rest))
    return rest


def _add_shape_triples_to_graph(ont_graph, sh_graph, property_type, prop, targets, shape_suffix):
    tgt_typ = SH_CLASS
    if shape_suffix == "DomainShape":
        tgt = SH.targetSubjectsOf
    else:
        tgt = SH.targetObjectsOf
        if property_type is OWL.DatatypeProperty:
            tgt_typ = SH.datatype

    for target in targets:
        sh_graph.add((URIRef(str(prop) + shape_suffix), RDF.type, SH.NodeShape), )
        sh_graph.add((URIRef(str(prop) + shape_suffix), tgt, prop))
        sh_graph.add((URIRef(str(prop) + shape_suffix), SH.severity, SH.Warning))
        if type(target) is BNode:
            item = ont_graph.value(subject=target, predicate=OWL.unionOf)
            if item:
                # add the shacl 'or' pointing to the list bnode
                sh_graph.add((URIRef(str(prop) + shape_suffix), SH_OR, item))
                # add triples for first item in the list
                rest = _insert_list_item(sh_graph, ont_graph, item, tgt_typ)
                # add triples for remaining list items
                while rest != RDF.nil:
                    item = rest
                    rest = _insert_list_item(sh_graph, ont_graph, item, tgt_typ)
        else:
            sh_graph.add((URIRef(str(prop) + shape_suffix), tgt_typ, target))


def _create_node_shapes_for_properties(ont_graph, sh_graph, property_type):
    for prop in ont_graph.subjects(predicate=RDF.type, object=property_type):
        # process domains
        targets = ont_graph.objects(subject=prop, predicate=RDFS.domain)
        shape_suffix = "DomainShape"
        _add_shape_triples_to_graph(ont_graph, sh_graph, property_type, prop, targets, shape_suffix)
        # process_ranges
        targets = ont_graph.objects(subject=prop, predicate=RDFS.range)
        shape_suffix = "RangeShape"
        _add_shape_triples_to_graph(ont_graph, sh_graph, property_type, prop, targets, shape_suffix)


def bind_restriction_values( ont_graph, restriction: Node):
    return {
                "path": ont_graph.value(subject=restriction, predicate=OWL.onProperty),
                "class": ont_graph.value(subject=restriction, predicate=OWL.onClass),
                "some": ont_graph.value(subject=restriction, predicate=OWL.someValuesFrom),
                "all_values": ont_graph.value(subject=restriction, predicate=OWL.allValuesFrom),
                "value": ont_graph.value(subject=restriction, predicate=OWL.hasValue),
                "minqc": ont_graph.value(subject=restriction, predicate=OWL.minQualifiedCardinality),
                "minc": ont_graph.value(subject=restriction, predicate=OWL.minCardinality),
                "maxqc": ont_graph.value(subject=restriction, predicate=OWL.maxQualifiedCardinality),
                "maxc": ont_graph.value(subject=restriction, predicate=OWL.maxCardinality),
                "qexact": ont_graph.value(subject=restriction, predicate=OWL.qualifiedCardinality),
                "exact": ont_graph.value(subject=restriction, predicate=OWL.cardinality),
                "union": ont_graph.value(subject=restriction, predicate=OWL.unionOf),
                "intersection": ont_graph.value(subject=restriction, predicate=OWL.intersectionOf),
                "first": ont_graph.value(subject=restriction, predicate=RDF.first),
                "rest": ont_graph.value(subject=restriction, predicate=RDF.rest)
    }

def add_restriction(ont_graph, sh_graph, item,  restriction):
    property_shape = BNode()
    if restriction["all_values"]:
        if type(item) is not BNode:
            sh_graph.add((URIRef(str(item) + 'Shape'), SH.property, property_shape))
        else:
            sh_graph.add((item, SH.property, property_shape))
        sh_graph.add((property_shape, SH.path, restriction["path"]))
        sh_graph.add((property_shape, SH_CLASS, restriction["all_values"]))
    elif restriction["some"]:
        if type(item) is not BNode:
            sh_graph.add((URIRef(str(item) + 'Shape'), SH.property, property_shape))
        else:
            property_shape = item
        sh_graph.add((property_shape, SH.path, restriction["path"]))
        sh_graph.add((property_shape, SH.minCount, Literal(1, datatype=XSD.nonNegativeInteger)))
        sh_graph.add((property_shape, SH_CLASS, restriction["some"]))
    elif restriction["union"]:
        if type(item) is not BNode:
            sh_graph.add((URIRef(str(item) + 'Shape'), SH_OR, restriction["union"]))
        else:
            sh_graph.add((item, SH_OR, restriction["union"]))
        item = restriction["union"]
        restriction_details = bind_restriction_values(ont_graph, item)
        add_restriction(ont_graph, sh_graph, item, restriction_details)
    elif restriction["intersection"]:
        if type(item) is not BNode:
            sh_graph.add((URIRef(str(item) + 'Shape'), SH_AND, restriction["intersection"]))
        else:
            sh_graph.add((item, SH_AND, restriction["intersection"]))
        item = restriction["intersection"]
        restriction_details = bind_restriction_values(ont_graph, item)
        add_restriction(ont_graph, sh_graph, item, restriction_details)
    elif restriction["first"]:
        sh_graph.add((item, RDF.first, restriction["first"]))
        sh_graph.add((item, RDF.rest, restriction["rest"]))
        item = restriction["first"]
        restriction_details = bind_restriction_values(ont_graph, item)
        add_restriction(ont_graph, sh_graph, item, restriction_details)
        if restriction["rest"] != RDF.nil:
            item = restriction["rest"]
            restriction_details = bind_restriction_values(ont_graph, item)
            add_restriction(ont_graph, sh_graph, item, restriction_details)
    else:
        if type(item) is not BNode:
            sh_graph.add((URIRef(str(item) + 'Shape'), SH.property, property_shape))
        else:
            sh_graph.add((item, SH.property, property_shape))

        if restriction["path"]: sh_graph.add((property_shape, SH.path, restriction["path"]))
        if restriction["class"]: sh_graph.add((property_shape, SH_CLASS, restriction["class"]))
        if restriction["value"]: sh_graph.add((property_shape, SH.hasValue, restriction["value"]))
        if restriction["minc"]: sh_graph.add((property_shape, SH.minCount, restriction["minc"]))
        if restriction["minqc"]: sh_graph.add((property_shape, SH.minCount, restriction["minqc"]))
        if restriction["maxc"]: sh_graph.add((property_shape, SH.maxCount, restriction["maxc"]))
        if restriction["maxqc"]: sh_graph.add((property_shape, SH.maxCount, restriction["maxqc"]))
        if restriction["exact"]:
            sh_graph.add((property_shape, SH.minCount, restriction["exact"]))
            sh_graph.add((property_shape, SH.maxCount, restriction["exact"]))
        if restriction["qexact"]:
            sh_graph.add((property_shape, SH.minCount, restriction["qexact"]))
            sh_graph.add((property_shape, SH.maxCount, restriction["qexact"]))


def _create_node_shapes_for_classes(ont_graph: Graph, sh_graph: Graph) -> None:
    rdf_classes = ont_graph.subjects(predicate=RDF.type, object=RDFS.Class)
    owl_classes = ont_graph.subjects(predicate=RDF.type, object=OWL.Class)
    classes = chain(rdf_classes, owl_classes)

    for item in classes:
        if type(item) is not BNode:  # only create shapes for identified classes
            sh_graph.add((URIRef(str(item) + 'Shape'), RDF.type, SH.NodeShape))
            sh_graph.add((URIRef(str(item) + 'Shape'), SH.targetClass, item))
            sh_graph.add((URIRef(str(item) + 'Shape'), SH.severity, SH.Warning))

            superclasses = ont_graph.objects(subject=item, predicate=RDFS.subClassOf)
            for superclass in superclasses:
                if type(superclass) is BNode:  # i.e. it is a restriction
                    restriction_details = bind_restriction_values(ont_graph, superclass)
                    add_restriction(ont_graph, sh_graph, item, restriction_details)


def create_shacl(ontology: str | Path | Graph) -> Tuple[Graph, Graph]:
    if isinstance(ontology, (Path, str)):
        ont_graph = Graph().parse(ontology)
    else:
        ont_graph = ontology
    sh_graph = Graph()
    # bind namespaces from ontology to shape graph
    for name, ns in ont_graph.namespaces():
        sh_graph.bind(name, ns, replace=True)

    _create_node_shapes_for_classes(ont_graph, sh_graph)
    _create_node_shapes_for_properties(ont_graph, sh_graph, OWL.ObjectProperty)
    _create_node_shapes_for_properties(ont_graph, sh_graph, OWL.DatatypeProperty)

    return ont_graph, sh_graph


def rdf_validate(data_file: str | Graph, ont_graph: str | Graph, sh_graph: str | Graph) -> Tuple[
        bool, Graph, str]:
    # run shacl validation
    conforms, results_graph, results_text = validate(data_file,
                                                     shacl_graph=sh_graph,
                                                     ont_graph=ont_graph,
                                                     inference='none',
                                                     abort_on_first=False,
                                                     allow_infos=False,
                                                     allow_warnings=False,
                                                     meta_shacl=False,
                                                     advanced=True,
                                                     js=False,
                                                     debug=False)

    return conforms, results_graph, results_text


def _parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("-o", "--ontology", help="Path to ontology - required", required=True)
    parser.add_argument("-v", "--validate", help="Path of file to validate", default=None)
    parser.add_argument("-s", "--shacl", help="Location for resulting shapes graph", default=None)

    return parser.parse_args()


def main(argv):
    args = _parse_args()
    if args.ontology:
        ont_graph, sh_graph = create_shacl(args.ontology)
        if args.shacl:
            if args.validate:
                conforms, results_graph, results_text = rdf_validate(args.validate, ont_graph, sh_graph)
                print(results_text)
            else:
                sh_graph.serialize(forat="turtle", destination=args.shacl)


if __name__ == "__main__":
    main(sys.argv[1:])

