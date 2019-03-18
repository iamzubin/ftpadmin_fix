#!/usr/bin/python
#
# A non-validating, semi-compliant parser for XML/RDF; it's meant
# to handle most things that would be in a DOAP file.
#
# Copyright (C) 2009  Red Hat, Inc
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 2
# of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, If not, see
# http://www.gnu.org/licenses/.
#
import re
import sys
import xml.sax
from xml.sax.saxutils import escape, quoteattr

DOAP = "http://usefulinc.com/ns/doap#"
FOAF = "http://xmlns.com/foaf/0.1/"
GNOME = "http://api.gnome.org/doap-extensions#"
RDF = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
XML = "http://www.w3.org/XML/1998/namespace"

WHITESPACE_RE = re.compile("\s+")

# Tag strings as urls
class UrlResource(str):
    pass

class ParseError(Exception):
    pass

class Node:
    def __init__(self, name, about=None):
        self.name  = name
        self.about = None
        self.properties = []

    def find_property(self, name, lang="en"):
        value = None
        for (n, l, v) in self.properties:
            if n == name:
                if l == lang:
                    return v
                elif l == None or value == None:
                    value = v

        return value

    def find_properties(self, name, lang="en"):
        value = None
        for (n, l, v) in self.properties:
            if n == name:
                if l == lang:
                    yield v
                elif l == None or value == None:
                    yield v

    def add_property(self, name, lang, value):
        self.properties.append((name, lang, value))

    def remove_property(self, name):
        self.properties = filter(lambda x: x[0] != name, self.properties)

class RdfHandler(xml.sax.handler.ContentHandler):
    def __init__(self):
        self.nodes = []
        self.__node_stack = []
        self.__property_stack = []
        self.__lang_stack = []
        self.__object = None
        self.__depth = 0

    def characters(self, s):
        if isinstance(self.__object, basestring):
            self.__object += s
        elif s.strip() != "":
            self.__object = s

    def startElementNS(self, name, qname, attributes):
        if name == (RDF, "RDF"):
            return

        self.__depth += 1
        try:
            lang = attributes.getValue((XML, "lang"))
        except KeyError:
            if self.__depth > 1:
                lang = self.__lang_stack[-1]
            else:
                lang = None
        self.__lang_stack.append(lang)

        if self.__depth % 2 == 0:
            node = None
            resource = None
            for attrname in attributes.getNames():
                if attrname == (XML, "lang"):
                    pass
                elif attrname == (RDF, "resource"):
                    resource = UrlResource(attributes.getValue(attrname))
                elif attrname == (RDF, "parseType"):
                    parseType = attributes.getValue(attrname)
                    if parseType == "resource":
                        if node == None:
                            node = Node(None)
                else:
                    if node == None:
                        node = Node(None)
                    node.properties.append((attrname, lang, attributes.getValue(attrname)))
            self.__property_stack.append((name, lang, resource))
            if node is not None:
                self.__node_stack.append(node)
                self.__depth += 1
        else:
            if not self.__object is None:
                raise ParseError()
            node = Node(name)
            self.__node_stack.append(node)
            for attrname in attributes.getNames():
                if attrname == (RDF, "about"):
                    node.about = attributes.getValue(attrname)
                else:
                    node.properties.append((attrname, lang, attributes.getValue(attrname)))

    def popProperty(self):
        (predicate, lang, resource) = self.__property_stack.pop()
        if self.__object:
            obj = self.__object
            if isinstance(obj, basestring):
                obj = obj.strip()
        else:
            obj = resource
        self.__object = None
        self.__node_stack[-1].properties.append((predicate, lang, obj))

    def popNode(self):
        node = self.__node_stack.pop()
        if self.__property_stack:
            self.__object = node
        self.nodes.append(node)
        return node

    def endElementNS(self, name, qname):
        if name == (RDF, "RDF"):
            return

        if self.__depth % 2 == 0:
            self.popProperty()
        else:
            node = self.popNode()
            if (node.name == None): # omitted blank node
                self.popProperty()
                self.__depth -= 1

        self.__lang_stack.pop()
        self.__depth -= 1

def read_rdf(f):
    handler = RdfHandler()

    parser = xml.sax.make_parser()
    parser.setContentHandler(handler)
    parser.setFeature(xml.sax.handler.feature_namespaces, 1)
    parser.parse(f)

    return handler.nodes

def qualname(name, namespaces):
    if name[0] is None:
        return name[1]
    else:
        return namespaces[name[0]] + ":" + name[1]

def _dump_node(f, node, lang, namespaces, depth=0):
    prefix = " " * depth
    if node.name != None:
        f.write(prefix)
        f.write('<%s' % qualname(node.name, namespaces))
        if node.about is not None:
            f.write(' rdf:about=%s' % quoteattr(node.about))
        f.write(">\n")

    for n, l, v in node.properties:
        f.write(prefix)
        f.write('  ')
        f.write('<%s' % qualname(n, namespaces))
        if l != lang:
            f.write(' xml:lang=%s' % quoteattr(l))
        if isinstance(v, UrlResource):
            f.write(' rdf:resource=%s' % quoteattr(v))
        elif isinstance(v, Node) and v.name == None:
            f.write(' rdf:parseType="resource"')

        if isinstance(v, UrlResource):
            f.write("/>\n")
        elif isinstance(v, basestring):
            f.write(">")
            if isinstance(v, str):
                f.write(escape(v))
            else:
                f.write(escape(v).encode("utf8"))
            f.write('</%s>\n' % qualname(n, namespaces))
        elif v == None:
            f.write("/>\n");
        else:
            f.write(">\n")
            _dump_node(f, v, l, namespaces, depth+4)
            f.write(prefix)
            f.write('  ')
            f.write('</%s>\n' % qualname(n, namespaces))

    if node.name != None:
        f.write(prefix)
        f.write('</%s>\n' % qualname(node.name, namespaces))

def dump_rdf(nodes, f):
    namespaces = {
        DOAP: 'doap',
        FOAF: 'foaf',
        GNOME: 'gnome',
        RDF: 'rdf',
        XML: 'xml'
    };

    namespace_count = 0
    toplevel_nodes = set(nodes)

    for node in nodes:
        if node.name and node.name[0] is not None and not node.name[0] in namespaces:
            namespace_count += 1
            namespaces[node.name[0]] = "ns" + str(namespace_count)
        for n, l, v in node.properties:
            if n[0] is not None and not n[0] in namespaces:
                namespace_count += 1
                namespaces[n[0]] = "ns" + str(namespace_count)
            if isinstance(v, Node):
                toplevel_nodes.remove(v)

    f.write("<?xml version='1.0' encoding='UTF-8'?>\n")
    f.write('<rdf:RDF')
    items = sorted(namespaces.items(), lambda x, y: cmp(x[1], y[1]))
    for url, name in items:
        if name != 'xml':
            f.write('\n    xmlns:%s="%s"' % (name, url))
    f.write('>\n')

    for node in toplevel_nodes:
        _dump_node(f, node, None, namespaces)

    f.write('</rdf:RDF>\n')

