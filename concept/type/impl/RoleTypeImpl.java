/*
 * Copyright (C) 2020 Grakn Labs
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 */

package hypergraph.concept.type.impl;

import hypergraph.common.exception.Error;
import hypergraph.common.exception.HypergraphException;
import hypergraph.common.iterator.Iterators;
import hypergraph.concept.type.RoleType;
import hypergraph.graph.TypeGraph;
import hypergraph.graph.util.Schema;
import hypergraph.graph.vertex.TypeVertex;

import javax.annotation.Nullable;
import java.util.Iterator;
import java.util.stream.Stream;

import static hypergraph.common.exception.Error.TypeWrite.INVALID_ROOT_TYPE_MUTATION;
import static java.util.Spliterator.IMMUTABLE;
import static java.util.Spliterator.ORDERED;
import static java.util.Spliterators.spliteratorUnknownSize;
import static java.util.stream.StreamSupport.stream;

public class RoleTypeImpl extends TypeImpl implements RoleType {

    private RoleTypeImpl(TypeVertex vertex) {
        super(vertex);
        assert vertex.schema() == Schema.Vertex.Type.ROLE_TYPE;
        if (vertex.schema() != Schema.Vertex.Type.ROLE_TYPE) {
            throw new HypergraphException(Error.TypeRead.TYPE_ROOT_MISMATCH.format(
                    vertex.label(),
                    Schema.Vertex.Type.ROLE_TYPE.root().label(),
                    vertex.schema().root().label()
            ));
        }
    }

    private RoleTypeImpl(TypeGraph graph, String label, String relation) {
        super(graph, label, Schema.Vertex.Type.ROLE_TYPE, relation);
    }

    public static RoleTypeImpl of(TypeVertex vertex) {
        if (vertex.label().equals(Schema.Vertex.Type.Root.ROLE.label())) return new RoleTypeImpl.Root(vertex);
        else return new RoleTypeImpl(vertex);
    }

    public static RoleTypeImpl of(TypeGraph graph, String label, String relation) {
        return new RoleTypeImpl(graph, label, relation);
    }

    void isAbstract(boolean isAbstract) {
        vertex.isAbstract(isAbstract);
    }

    void sup(RoleType superType) {
        super.superTypeVertex(((RoleTypeImpl) superType).vertex);
    }

    @Nullable
    @Override
    public RoleTypeImpl sup() {
        TypeVertex vertex = super.superTypeVertex();
        return vertex != null ? of(vertex) : null;
    }

    @Override
    public Stream<RoleTypeImpl> sups() {
        Iterator<RoleTypeImpl> sups = Iterators.apply(super.superTypeVertices(), RoleTypeImpl::of);
        return stream(spliteratorUnknownSize(sups, ORDERED | IMMUTABLE), false);
    }

    @Override
    public Stream<RoleTypeImpl> subs() {
        Iterator<RoleTypeImpl> subs = Iterators.apply(super.subTypeVertices(), RoleTypeImpl::of);
        return stream(spliteratorUnknownSize(subs, ORDERED | IMMUTABLE), false);
    }

    @Override
    public String scopedLabel() {
        return vertex.scopedLabel();
    }

    public static class Root extends RoleTypeImpl {

        Root(TypeVertex vertex) {
            super(vertex);
            assert vertex.label().equals(Schema.Vertex.Type.Root.ROLE.label());
        }

        @Override
        public boolean isRoot() { return true; }

        @Override
        public void label(String label) { throw new HypergraphException(INVALID_ROOT_TYPE_MUTATION); }

        @Override
        void isAbstract(boolean isAbstract) { throw new HypergraphException(INVALID_ROOT_TYPE_MUTATION); }

        @Override
        void sup(RoleType superType) { throw new HypergraphException(INVALID_ROOT_TYPE_MUTATION); }
    }
}
