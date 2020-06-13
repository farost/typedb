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

package hypergraph.test.behaviour.concept.thing;

import hypergraph.concept.thing.Thing;
import hypergraph.concept.type.ThingType;
import hypergraph.test.behaviour.config.Parameters.RootLabel;
import io.cucumber.java.After;
import io.cucumber.java.en.Then;
import io.cucumber.java.en.When;

import java.util.HashMap;
import java.util.Map;

import static hypergraph.test.behaviour.concept.type.thingtype.ThingTypeSteps.get_thing_type;
import static hypergraph.test.behaviour.connection.ConnectionSteps.tx;
import static java.util.Objects.isNull;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class ThingSteps {

    private static Map<String, Thing> things = new HashMap<>();

    public static Thing get(String variable) {
        return things.get(variable);
    }

    public static void put(String variable, Thing thing) {
        things.put(variable, thing);
    }

    public static void remove(String variable) {
        things.remove(variable);
    }

    @Then("entity/attribute/relation {var} is null: {bool}")
    public void thing_is_null(String var, boolean isNull) {
        assertEquals(isNull, isNull(get(var)));
    }

    @Then("{root_label} {var} has type: {type_label}")
    public void thing_has_type(RootLabel rootLabel, String var, String typeLabel) {
        ThingType type = get_thing_type(rootLabel, typeLabel);
        assertEquals(type, get(var).type());
    }

    @When("delete entity:/attribute:/relation: {var}")
    public void thing_is_deleted(String var) {
        get(var).delete();
    }

    @When("entity/attribute/relation {var} set key: {var}")
    public void thing_set_key(String var1, String var2) {
        get(var1).has(get(var2).asAttribute());
    }

    @When("entity/attribute/relation {var} get keys\\( ?{type_label} ?) contain: {var}")
    public void thing_get_keys_contains(String var1, String typeLabel, String var2) {
        assertTrue(get(var1).keys(tx().concepts().getAttributeType(typeLabel)).anyMatch(k -> k.equals(get(var2))));
    }

    @When("entity/attribute/relation {var} get keys contain: {var}")
    public void thing_get_keys_contains(String var1, String var2) {
        assertTrue(get(var1).keys().anyMatch(k -> k.equals(get(var2))));
    }

    @After
    public void clear() {
        things.clear();
    }
}
