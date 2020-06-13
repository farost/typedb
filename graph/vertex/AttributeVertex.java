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

package hypergraph.graph.vertex;

import hypergraph.graph.iid.VertexIID;
import hypergraph.graph.util.Schema;

import java.time.LocalDateTime;

public interface AttributeVertex<VALUE> extends ThingVertex {

    /**
     * Returns the IID of this {@code AttributeVertex}.
     *
     * @return the IID of this {@code AttributeVertex}
     */
    @Override
    VertexIID.Attribute<VALUE> iid();

    /**
     * Returns the {@code ValueType} of this {@code Attribute}
     *
     * @return the {@code ValueType} of this {@code Attribute}
     */
    Schema.ValueType valueType();

    /**
     * Returns the literal value stored in the vertex, if it represents an attribute.
     *
     * @return the literal value stored in the vertex
     */
    VALUE value();

    AttributeVertex<Boolean> asBoolean();

    AttributeVertex<Long> asLong();

    AttributeVertex<Double> asDouble();

    AttributeVertex<String> asString();

    AttributeVertex<LocalDateTime> asDateTime();
}
