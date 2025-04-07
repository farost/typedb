# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

#noinspection CucumberUndefinedStep
Feature: TypeQL Match Clause

  Background: Open connection and create a simple extensible schema
    Given typedb starts
    Given connection opens with default authentication
    Given connection is open: true
    Given connection has 0 databases
    Given connection create database: typedb
    Given connection open schema transaction for database: typedb

    Given typeql schema query
      """
      define
      entity person
        plays friendship:friend,
        plays employment:employee,
        owns name @card(0..),
        owns age @card(0..),
        owns ref @key,
        owns email @unique @card(0..);
      entity company
        plays employment:employer,
        owns name @card(0..),
        owns ref @key;
      relation friendship
        relates friend @card(0..),
        owns ref @key;
      relation employment
        relates employee @card(0..),
        relates employer @card(0..),
        owns ref @key;
      attribute name value string;
      attribute age @independent, value integer;
      attribute ref value integer;
      attribute email value string;
      """
    Given transaction commits

    Given connection open schema transaction for database: typedb


  #############
  # RELATIONS #
  #############

  Scenario: relation types without role types can be matched
    Given typeql schema query
      """
      define relation loneliness;
      """
    When get answers of typeql read query
      """
      match $r label loneliness;
      """
    Then uniquely identify answer concepts
      | r                |
      | label:loneliness |
    When get answers of typeql read query
      """
      match relation $r;
      """
    Then uniquely identify answer concepts
      | r                |
      | label:friendship |
      | label:employment |
      | label:loneliness |
    When get answers of typeql read query
      """
      match not {$_ isa $r;}; relation $r;
      """
    Then uniquely identify answer concepts
      | r                |
      | label:friendship |
      | label:employment |
      | label:loneliness |
#
#
#  Scenario: a relation is matchable from role players without specifying relation type
#    Given transaction commits
#
#    Given connection open write transaction for database: typedb
#    Given typeql write query
#      """
#      insert
#      $x isa person, has ref 0;
#      $y isa company, has ref 1;
#      $r isa employment,
#        links (employee: $x, employer: $y),
#        has ref 2;
#      """
#    Given transaction commits
#
#    Given connection open read transaction for database: typedb
#    Then get answers of typeql read query
#      """
#      match $x isa person; $r links (employee: $x);
#      """
#    Then uniquely identify answer concepts
#      | x         | r         |
#      | key:ref:0 | key:ref:2 |
#    When get answers of typeql read query
#      """
#      match $y isa company; $r links (employer: $y);
#      """
#    Then uniquely identify answer concepts
#      | y         | r         |
#      | key:ref:1 | key:ref:2 |
#
#
#  Scenario: relations are matchable from roleplayers without specifying any roles
#    Given transaction commits
#
#    Given connection open write transaction for database: typedb
#    Given typeql write query
#      """
#      insert
#      $x isa person, has ref 0;
#      $y isa company, has ref 1;
#      $r links (employee: $x, employer: $y), isa employment,
#         has ref 2;
#      """
#    Given transaction commits
#
#    Given connection open read transaction for database: typedb
#    When get answers of typeql read query
#      """
#      match $x isa person; $r links ($x);
#      """
#    Then uniquely identify answer concepts
#      | x         | r         |
#      | key:ref:0 | key:ref:2 |
#
#
#  Scenario: all combinations of players in a relation can be retrieved
#    Given transaction commits
#
#    Given connection open write transaction for database: typedb
#    When typeql write query
#       """
#       insert $p isa person, has ref 0;
#       $c isa company, has ref 1;
#       $c2 isa company, has ref 2;
#       $r links (employee: $p, employer: $c, employer: $c2), isa employment, has ref 3;
#       """
#    Given transaction commits
#
#    Given connection open read transaction for database: typedb
#    Then get answers of typeql read query
#       """
#       match $r links ($x, $y), isa employment;
#       """
#     # here
#    Then uniquely identify answer concepts
#      | x         | y         | r         |
#      | key:ref:0 | key:ref:1 | key:ref:3 |
#      | key:ref:1 | key:ref:0 | key:ref:3 |
#      | key:ref:0 | key:ref:2 | key:ref:3 |
#      | key:ref:2 | key:ref:0 | key:ref:3 |
#      | key:ref:1 | key:ref:2 | key:ref:3 |
#      | key:ref:2 | key:ref:1 | key:ref:3 |
#
#
#   # TODO: 3.x: this should only be possible with ordered role players?
#  @ignore
#  Scenario: repeated role players are retrieved singly when queried doubly
#    Given typeql schema query
#       """
#       define
#       entity some-entity plays symmetric:player, owns ref @key;
#       relation symmetric relates player, owns ref @key;
#       """
#    Given transaction commits
#
#    Given connection open write transaction for database: typedb
#    Given typeql write query
#       """
#       insert $x isa some-entity, has ref 0; symmetric (player: $x, player: $x), has ref 1;
#       """
#    Given transaction commits
#
#    Given connection open read transaction for database: typedb
#    When get answers of typeql read query
#       """
#       match $r links (player: $x, player: $x);
#       """
#    Then uniquely identify answer concepts
#      | x         | r         |
#      | key:ref:0 | key:ref:1 |
#
##
##  Scenario: repeated role players are retrieved singly when queried singly
##    Given typeql schema query
##      """
##      define
##      entity some-entity plays symmetric:player, owns ref @key;
##      relation symmetric relates player, owns ref @key;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert $x isa some-entity, has ref 0; symmetric (player: $x, player: $x), has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $r links (player: $x);
##      """
##    Then uniquely identify answer concepts
##      | x         | r         |
##      | key:ref:0 | key:ref:1 |
##
##
##  Scenario: a mixture of variable and explicit roles can retrieve relations
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa company, has ref 0;
##       $y isa person, has ref 1;
##       (employer: $x, employee: $y) isa employment, has ref 2;
##       """
##    Given transaction commits
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match (employer: $e, $role: $x) isa employment;
##       """
##    Then uniquely identify answer concepts
##      | e         | x         | role                      |
##      | key:ref:0 | key:ref:1 | label:employment:employee |
##
##
##  Scenario: A relation can play a role in itself
##    Given typeql schema query
##      """
##      define
##      relation comparator
##        relates compared,
##        plays comparator:compared;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $r isa comparator (compared:$r);
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $r isa comparator (compared:$r);
##      """
##    Then answer size is: 1
##
##
##  Scenario: A relation can play a role in itself and have additional roleplayers
##    Given typeql schema query
##      """
##      define
##      relation comparator
##        relates compared @card(0..),
##        plays comparator:compared;
##      entity variable
##        plays comparator:compared;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $r isa comparator (compared: $v, compared:$r);
##      $v isa variable;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $r  isa comparator (compared: $v, compared:$r);
##      """
##    Then answer size is: 1
##
##
##  Scenario: relations between distinct concepts are not retrieved when matching concepts that relate to themselves
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa person, has ref 1;
##       $y isa person, has ref 2;
##       (friend: $x, friend: $y) isa friendship, has ref 0;
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match (friend: $x, friend: $x) isa friendship;
##       """
##    Then answer size is: 0
##
##
##  Scenario: matching a chain of relations only returns answers if there is a chain of the required length
##    Given typeql schema query
##      """
##      define
##
##      relation gift-delivery
##        relates sender @card(0..),
##        relates recipient @card(0..);
##
##      person plays gift-delivery:sender,
##        plays gift-delivery:recipient;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x1 isa person, has name "Soroush", has ref 0;
##      $x2a isa person, has name "Martha", has ref 1;
##      $x2b isa person, has name "Patricia", has ref 2;
##      $x2c isa person, has name "Lily", has ref 3;
##
##      gift-delivery (sender: $x1, recipient: $x2a);
##      gift-delivery (sender: $x1, recipient: $x2b);
##      gift-delivery (sender: $x1, recipient: $x2c);
##      gift-delivery (sender: $x2a, recipient: $x2b);
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        gift-delivery (sender: $a, recipient: $b);
##        gift-delivery (sender: $b, recipient: $c);
##      """
##    Then uniquely identify answer concepts
##      | a         | b         | c         |
##      | key:ref:0 | key:ref:1 | key:ref:2 |
##    When get answers of typeql read query
##      """
##      match
##        gift-delivery (sender: $a, recipient: $b);
##        gift-delivery (sender: $b, recipient: $c);
##        gift-delivery (sender: $c, recipient: $d);
##      """
##    Then answer size is: 0
##
##
##  Scenario: when multiple relation instances exist with the same roleplayer, matching that player returns just 1 answer
##    Given typeql schema query
##       """
##       define
##       relation residency
##         relates resident,
##         owns ref @key;
##       person plays residency:resident;
##       """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa person, has ref 0;
##       $e links (employee: $x), isa employment, has ref 1;
##       $f links (friend: $x), isa friendship, has ref 2;
##       $r links (resident: $x), isa residency, has ref 3;
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##       """
##       match relation $t; $r isa $t;
##       """
##    Given uniquely identify answer concepts
##      | r         |
##      | key:ref:1 |
##      | key:ref:2 |
##      | key:ref:3 |
##    When get answers of typeql read query
##       """
##       match ($x) isa $_;
##       """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##    When get answers of typeql read query
##       """
##       match ($x);
##       """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##
##  Scenario: an error is thrown when matching an entity type as if it were a role type
##    Then typeql read query; fails
##      """
##      match (person: $x);
##      """
##    Then transaction is open: true
##
##
##  Scenario: an error is thrown when matching an entity type as if it were a relation type
##    Then typeql read query; fails
##      """
##      match person ($x);
##      """
##    Then transaction is open: true
##
##
##  Scenario: an error is thrown when matching a non-existent type label as if it were a relation type
##    Then typeql read query; fails
##      """
##      match bottle-of-rum ($x);
##      """
##    Then transaction is open: true
##
##
##  Scenario: when matching a role type that doesn't exist, an error is thrown
##    Then typeql read query; fails
##      """
##      match (rolein-rolein-rolein: $rolein);
##      """
##    Then transaction is open: true
##
##
##  Scenario: when matching a role in a relation type that doesn't have that role, an error is thrown
##    Then typeql read query; fails
##      """
##      match employment (friend: $x);
##      """
##    Then transaction is open: true
##
##
##  Scenario: when matching a roleplayer in a relation that can't actually play that role, an error is thrown
##    When typeql read query; fails
##      """
##      match
##      $x isa company;
##      friendship ($x);
##      """
##    Then transaction is open: true
##
##  # TODO: 3.x: Do we not want to allow multiple specialistaions of the same role?
##  # [SVL13] Relation type 'hetero-marriage' is already specialised by a supertype for 'marriage:spouse'
##  @ignore
##  Scenario: Relations can be queried with pairings of relation and role types that are not directly related to each other
##    Given typeql schema query
##       """
##       define
##       person plays marriage:spouse, plays hetero-marriage:husband, plays hetero-marriage:wife;
##       relation marriage relates spouse @card(0..);
##       relation hetero-marriage sub marriage, relates husband as spouse, relates wife as spouse;
##       relation civil-marriage sub marriage;
##       """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $a isa person, has ref 1;
##       $b isa person, has ref 2;
##       (wife: $a, husband: $b) isa hetero-marriage;
##       (spouse: $a, spouse: $b) isa civil-marriage;
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $m links (wife: $x, husband: $y), isa hetero-marriage;
##       """
##    Then answer size is: 1
##    Then typeql read query; fails
##       """
##       match $m links (wife: $x, husband: $y), isa civil-marriage;
##       """
##    Then transaction is open: false
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $m links (wife: $x, husband: $y), isa marriage;
##       """
##    Then answer size is: 1
##    When get answers of typeql read query
##       """
##       match $m links (wife: $x, husband: $y);
##       """
##    Then answer size is: 1
##    When get answers of typeql read query
##       """
##       match $m links (spouse: $x, spouse: $y), isa hetero-marriage;
##       """
##    Then answer size is: 2
##    When get answers of typeql read query
##       """
##       match $m links (spouse: $x, spouse: $y), isa civil-marriage;
##       """
##    Then answer size is: 2
##    When get answers of typeql read query
##       """
##       match $m links (spouse: $x, spouse: $y), isa marriage;
##       """
##    Then answer size is: 4
##    When get answers of typeql read query
##       """
##       match $m links (spouse: $x, spouse: $y);
##       """
##    Then answer size is: 4
##    When get answers of typeql read query
##       """
##       match $m links (role: $x, role: $y), isa hetero-marriage;
##       """
##    Then answer size is: 2
##    When get answers of typeql read query
##       """
##       match $m links (role: $x, role: $y), isa civil-marriage;
##       """
##    Then answer size is: 2
##    When get answers of typeql read query
##       """
##       match $m links (role: $x, role: $y), isa marriage;
##       """
##    Then answer size is: 4
##    When get answers of typeql read query
##       """
##       match $m links (role: $x, role: $y);
##       """
##    Then answer size is: 4
##
##
##  Scenario: When some relations do not satisfy the query, the correct ones are still found
##    Given typeql schema query
##      """
##      define
##      entity car plays ownership:owned, owns ref @key;
##      person plays ownership:owner;
##      company plays ownership:owner;
##      relation ownership relates owned, relates owner, owns is-insured;
##      attribute is-insured value boolean;
##      """
##    Given transaction commits
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      ownership (owned: $c1, owner: $company), has is-insured true;
##      $c1 isa car, has ref 0; $company isa company, has ref 1;
##      """
##    Given transaction commits
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      ownership (owned: $c2, owner: $person), has is-insured true;
##      $c2 isa car, has ref 2; $person isa person, has ref 3;
##      """
##    Given transaction commits
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##    """
##    match $r links (owner: $x), isa ownership, has is-insured true; $x isa person;
##    """
##    Then answer size is: 1
##
##
### TODO: 3.x: Uncomment "as!" steps when it is implemented
##  Scenario: match 'as' pattern works similarly to `sub`
##    Given typeql schema query
##      """
##      define
##      relation parentship relates parent, relates child;
##      relation fathership sub parentship, relates father as parent, relates father-child as child;
##      relation adoption relates adopter, relates adoptee;
##      relation child-adoption sub adoption, relates child as adoptee;
##      relation boy-adoption sub child-adoption, relates boy as child;
##      """
##    Given transaction commits
##
##    When connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##      $x relates $_ as parentship:child;
##      """
##    Then uniquely identify answer concepts
##      | x                |
##      | label:fathership |
##      | label:parentship |
##
###    When get answers of typeql read query
###      """
###      match
###      $x relates $_ as! parentship:child;
###      """
###    Then uniquely identify answer concepts
###      | x                |
###      | label:fathership |
##
##    When get answers of typeql read query
##      """
##      match
##      $x relates $_ as child;
##      """
##    Then uniquely identify answer concepts
##      | x                    |
##      | label:parentship     |
##      | label:fathership     |
##      | label:boy-adoption   |
##      | label:child-adoption |
##
###    When get answers of typeql read query
###      """
###      match
###      $x relates $_ as! child;
###      """
###    Then uniquely identify answer concepts
###      | x                  |
###      | label:fathership   |
###      | label:boy-adoption |
##
##    When get answers of typeql read query
##      """
##      match
##      $x relates $_ as parentship:parent;
##      """
##    Then uniquely identify answer concepts
##      | x                |
##      | label:parentship |
##      | label:fathership |
##
###    When get answers of typeql read query
###      """
###      match
###      $x relates $_ as! parentship:parent;
###      """
###    Then uniquely identify answer concepts
###      | x                |
###      | label:fathership |
##
##    When get answers of typeql read query
##      """
##      match
##      $x relates $_ as parent;
##      """
##    Then uniquely identify answer concepts
##      | x                |
##      | label:parentship |
##      | label:fathership |
##
###    When get answers of typeql read query
###      """
###      match
###      $x relates $_ as! parent;
###      """
###    Then uniquely identify answer concepts
###      | x                |
###      | label:fathership |
##
##    When get answers of typeql read query
##      """
##      match
##      $_ relates $x as parentship:child;
##      """
##    Then uniquely identify answer concepts
##      | x                             |
##      | label:parentship:child        |
##      | label:fathership:father-child |
##
##    When get answers of typeql read query
##      """
##      match
##      $y relates $x;
##      $x sub parentship:child;
##      """
##    Then uniquely identify answer concepts
##      | x                             | y                |
##      | label:parentship:child        | label:parentship |
##      | label:parentship:child        | label:fathership |
##      | label:fathership:father-child | label:fathership |
##
###    When get answers of typeql read query
###      """
###      match
###      $_ relates $x as! parentship:child;
###      """
###    Then uniquely identify answer concepts
###      | x                  |
###      | label:fathership:father-child |
##
##    When get answers of typeql read query
##      """
##      match
##      $y relates $x;
##      $x sub! parentship:child;
##      """
##    Then uniquely identify answer concepts
##      | x                             | y                |
##      | label:fathership:father-child | label:fathership |
##
##    When get answers of typeql read query
##      """
##      match
##      $_ relates $x as child;
##      """
##    Then uniquely identify answer concepts
##      | x                             |
##      | label:parentship:child        |
##      | label:fathership:father-child |
##      | label:child-adoption:child    |
##      | label:boy-adoption:boy        |
##
###    When get answers of typeql read query
###      """
###      match
###      $_ relates $x as! child;
###      """
###    Then uniquely identify answer concepts
###      | x                             |
###      | label:fathership:father-child |
###      | label:boy-adoption:boy        |
##
##    When get answers of typeql read query
##      """
##      match
##      $_ relates $x as parentship:parent;
##      """
##    Then uniquely identify answer concepts
##      | x                       |
##      | label:parentship:parent |
##      | label:fathership:father |
##
###    When get answers of typeql read query
###      """
###      match
###      $_ relates $x as! parentship:parent;
###      """
###    Then uniquely identify answer concepts
###      | x                       |
###      | label:fathership:father |
##
##    When get answers of typeql read query
##      """
##      match
##      $_ relates $x as parent;
##      """
##    Then uniquely identify answer concepts
##      | x                       |
##      | label:parentship:parent |
##      | label:fathership:father |
##
###    When get answers of typeql read query
###      """
###      match
###      $_ relates $x as! parent;
###      """
###    Then uniquely identify answer concepts
###      | x                       |
###      | label:fathership:father |
##
##  ##############
##  # ATTRIBUTES #
##  ##############
##
##  Scenario: match value pattern works for all built-in value types
##    Given typeql schema query
##      """
##      define
##      attribute root @abstract;
##      attribute age, value integer;
##      attribute name, value string;
##      attribute is-new, value boolean;
##      attribute success, value double;
##      attribute balance, value decimal;
##      attribute birth-date, value date;
##      attribute birth-time, value datetime;
##      attribute current-time, value datetime-tz;
##      attribute expiration, value duration;
##      """
##    Given transaction commits
##
##    Given connection open schema transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##      $lo value integer;
##      $st value string;
##      $bo value boolean;
##      $do value double;
##      $de value decimal;
##      $date value date;
##      $datet value datetime;
##      $datet-t value datetime-tz;
##      $du value duration;
##
##      not { $st label email; };
##      not { $lo label ref; };
##      """
##    Then uniquely identify answer concepts
##      | lo        | st         | bo           | do            | de            | date             | datet            | datet-t            | du               |
##      | label:age | label:name | label:is-new | label:success | label:balance | label:birth-date | label:birth-time | label:current-time | label:expiration |
##
##    When typeql schema query
##      """
##      define
##      balance @abstract;
##      attribute shared-balance @abstract, sub balance;
##      attribute family-surname sub shared-balance;
##      attribute loading-time sub root, value duration;
##      """
##    When transaction commits
##
##    When connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##      $de value decimal;
##      """
##    Then uniquely identify answer concepts
##      | de                   |
##      | label:balance        |
##      | label:shared-balance |
##      | label:family-surname |
##
##    When get answers of typeql read query
##      """
##      match
##      $du value duration;
##      """
##    Then uniquely identify answer concepts
##      | du                 |
##      | label:expiration   |
##      | label:loading-time |
##
##    When get answers of typeql read query
##      """
##      match
##      $datet value datetime;
##      """
##    Then uniquely identify answer concepts
##      | datet            |
##      | label:birth-time |
##
##
##  Scenario Outline: '<type>' attributes can be matched by value
##    Given typeql schema query
##       """
##       define attribute <attr> @independent, value <type>;
##       """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert $n isa <attr> <value>;
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $a isa <attr> <value>;
##       """
##    Then uniquely identify answer concepts
##      | a                   |
##      | attr:<attr>:<value> |
##
##    Examples:
##      | attr              | type        | value                              |
##      | is-alive          | boolean     | true                               |
##      | age               | integer     | 21                                 |
##      | score             | double      | 123.456                            |
##      | balance           | decimal     | 123.456dec                         |
##      | name              | string      | "alice"                            |
##      | birth-date        | date        | 1990-01-01                         |
##      | event-datetime    | datetime    | 1990-01-01T11:22:33.123456789      |
##      | global-date       | datetime-tz | 1990-01-01T11:22:33 Asia/Kathmandu |
##      | global-date       | datetime-tz | 1990-01-01T11:22:33-0100           |
##      | schedule-interval | duration    | P1Y2M3DT4H5M6.789S                 |
##      | schedule-interval | duration    | P1Y2M3DT4H5M6S                     |
##
##
##    # TODO: Add tests for structs
##
##
##  Scenario Outline: when matching a '<type>' attribute by a value that doesn't exist, an empty answer is returned
##    Given typeql schema query
##      """
##      define attribute <attr> value <type>;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $a isa <attr> <value>;
##      """
##    Then answer size is: 0
##
##    Examples:
##      | attr        | type        | value                    |
##      | colour      | string      | "Green"                  |
##      | calories    | integer     | 1761                     |
##      | grams       | double      | 9.6                      |
##      | gluten-free | boolean     | false                    |
##      | use-by-date | datetime    | 2020-06-16               |
##      | global-date | datetime-tz | 1990-01-01T11:22:33-0100 |
##      | interval    | duration    | P1Y2M3DT4H5M6.789S       |
##
##
##  Scenario: 'contains' matches strings that contain the specified substring
##    Given typeql schema query
##    """
##    define
##    attribute name @independent, value string;
##    """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa name "Seven Databases in Seven Weeks";
##       $y isa name "Four Weddings and a Funeral";
##       $z isa name "Fun Facts about Space";
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $x isa name contains "Fun";
##       """
##    Then uniquely identify answer concepts
##      | x                                     |
##      | attr:name:Four Weddings and a Funeral |
##      | attr:name:Fun Facts about Space       |
##
##
##  # NOTE for implementation: we should be using Unicode full case folding for this, not just `.to_lowercase`
##  Scenario: 'contains' performs a case-insensitive match
##    Given typeql schema query
##    """
##    define
##    attribute name @independent, value string;
##    """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa name "The Phantom of the Opera";
##       $y isa name "Pirates of the Caribbean";
##       $z isa name "Mr. Bean";
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $x isa name contains "Bean";
##       """
##    Then uniquely identify answer concepts
##      | x                                  |
##      | attr:name:Pirates of the Caribbean |
##      | attr:name:Mr. Bean                 |
##
##
##  Scenario: 'like' matches strings that match the specified regex
##    Given typeql schema query
##    """
##    define
##    attribute name @independent, value string;
##    """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa name "ABC123";
##       $y isa name "123456";
##       $z isa name "9";
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##       """
##       match $x isa name like "^[0-9]+$";
##       """
##    Then uniquely identify answer concepts
##      | x                |
##      | attr:name:123456 |
##      | attr:name:9      |
##
##
##  Scenario: 'like' expects string literals as regex
##    Given transaction closes
##    Given connection open read transaction for database: typedb
##    Then typeql read query; fails with a message containing: "Expected a string literal as regex"
##    """
##    match
##    let $x = "alice@example.com";
##    $x like 12;
##    """
##    Then typeql read query; fails with a message containing: "Expected a string literal as regex"
##    """
##    match
##    let $x = "alice@example.com";
##    let $regex = "[a-z]+@[a-z]+\\.[a-z]+";
##    $x like $regex;
##    """
##    Then typeql read query; fails with a message containing: "The regular expression failed compilation: '[a-z+@[a-z]+\.[a-z]+'."
##    """
##    match
##    let $x = "alice@example.com";
##    $x like "[a-z+@[a-z]+\\.[a-z]+";
##    """
##    When get answers of typeql read query
##    """
##    match
##    let $x = "alice@example.com";
##    $x like "[a-z]+@[a-z]+\\.[a-z]+";
##    """
##    Then answer size is: 1
##    When get answers of typeql read query
##    """
##    match
##    let $x = "alice@local";
##    $x like "[a-z]+@[a-z]+\\.[a-z]+";
##    """
##    Then answer size is: 0
##
##
##   # TODO: 3.x: Do we need a more realistic IID for the attribute?
##  Scenario: when querying for a non-existent attribute type iid, an empty result is returned
##    When get answers of typeql read query
##      """
##      match $x has name $y; $x iid 0x1e00000000001234567890;
##      """
##    Then answer size is: 0
##    When get answers of typeql read query
##      """
##      match $x has name $y; $y iid 0x1e00000000001234567890;
##      """
##    Then answer size is: 0
##
##  # TODO: this test uses attributes, but is ultimately testing the traversal structure,
##  #       such that match query does not throw. Perhaps we should introduce a new feature file
##  #       containing a new set of scenarios that test: traversal structure, plan and procedure
##  Scenario: Traversal planner can handle "loops" in the traversal structure
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name 'alice', has ref 0;
##      $y isa person, has name 'alice', has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##      $x isa person, has $n;
##      $y isa person, has $n;
##      """
##
##  Scenario: `isa!` matches only attributes of the specific type, while `isa` all attributes of this type and subtypes
##    Given transaction commits
##
##    Given connection open schema transaction for database: typedb
##    Given typeql schema query
##      """
##      define
##      attribute valueless-name @abstract;
##      name sub valueless-name;
##      attribute first-name sub name;
##      attribute second-name sub name;
##      attribute passport-first-name sub first-name;
##      person owns first-name @card(0..2), owns second-name, owns passport-first-name;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person,
##        has name "Allie Morgan",
##        has first-name "Allie",
##        has second-name "Morgan",
##        has passport-first-name "Alice",
##        has ref 0;
##      """
##    Given transaction commits
##    Given connection open read transaction for database: typedb
##
##    When get answers of typeql read query
##      """
##      match $a isa valueless-name;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:name:"Allie Morgan"         |
##      | attr:first-name:"Allie"          |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##    Then typeql read query; fails with a message containing: "empty-set for some variable"
##      """
##      match $a isa! valueless-name;
##      """
##    When transaction closes
##    When connection open read transaction for database: typedb
##
##    When get answers of typeql read query
##      """
##      match $a isa name;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:name:"Allie Morgan"         |
##      | attr:first-name:"Allie"          |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $a isa! name;
##      """
##    Then uniquely identify answer concepts
##      | a                        |
##      | attr:name:"Allie Morgan" |
##
##    When get answers of typeql read query
##      """
##      match $a isa first-name;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:first-name:"Allie"          |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $a isa! first-name;
##      """
##    Then uniquely identify answer concepts
##      | a                       |
##      | attr:first-name:"Allie" |
##
##    When get answers of typeql read query
##      """
##      match $a isa second-name;
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match $a isa! second-name;
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match $a isa passport-first-name;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $a isa! passport-first-name;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      not { $a isa passport-first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:name:"Allie Morgan"  |
##      | attr:first-name:"Allie"   |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      not { $a isa! passport-first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:name:"Allie Morgan"  |
##      | attr:first-name:"Allie"   |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      not { $a isa first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:name:"Allie Morgan"  |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      not { $a isa! first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:name:"Allie Morgan"         |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##  Scenario: Not owned attributes can be matched only if their types are independent
##    Given transaction commits
##
##    Given connection open schema transaction for database: typedb
##    Given typeql schema query
##      """
##      define
##      attribute valueless-name @abstract @independent;
##      attribute name value string, sub valueless-name;
##
##      attribute age @independent, value integer;
##      attribute dog-age sub age;
##
##      attribute birth-info @abstract;
##      attribute birth-date value date, sub birth-info;
##      attribute official-birth-date sub birth-date;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    When get answers of typeql write query
##      """
##      insert
##      $n isa name "Bob"; # independent: inherited
##      $a isa age 25; # independent: declared
##      $da isa dog-age 7; # independent: inherited
##      $bd isa birth-date 2025-02-11; # not independent
##      $obd isa official-birth-date 2025-02-12; # not independent
##      """
##    Then uniquely identify answer concepts
##      | n               | a           | da             | bd                         | obd                                 |
##      | attr:name:"Bob" | attr:age:25 | attr:dog-age:7 | attr:birth-date:2025-02-11 | attr:official-birth-date:2025-02-12 |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:age:25    |
##      | attr:dog-age:7 |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! age;
##      """
##    Then uniquely identify answer concepts
##      | a           |
##      | attr:age:25 |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa dog-age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:dog-age:7 |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! dog-age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:dog-age:7 |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa birth-date;
##      """
##    Then answer size is: 0
##    When get answers of typeql read query
##      """
##      match
##      $a isa! birth-date;
##      """
##    Then answer size is: 0
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa official-birth-date;
##      """
##    Then answer size is: 0
##    When get answers of typeql read query
##      """
##      match
##      $a isa! official-birth-date;
##      """
##    Then answer size is: 0
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa valueless-name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa birth-info;
##      """
##    Then answer size is: 0
##
##    When transaction commits
##    When connection open read transaction for database: typedb
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:age:25    |
##      | attr:dog-age:7 |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! age;
##      """
##    Then uniquely identify answer concepts
##      | a           |
##      | attr:age:25 |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa dog-age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:dog-age:7 |
##    When get answers of typeql read query
##      """
##      match
##      $a isa! dog-age;
##      """
##    Then uniquely identify answer concepts
##      | a              |
##      | attr:dog-age:7 |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa birth-date;
##      """
##    Then answer size is: 0
##    When get answers of typeql read query
##      """
##      match
##      $a isa! birth-date;
##      """
##    Then answer size is: 0
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa official-birth-date;
##      """
##    Then answer size is: 0
##    When get answers of typeql read query
##      """
##      match
##      $a isa! official-birth-date;
##      """
##    Then answer size is: 0
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa valueless-name;
##      """
##    Then uniquely identify answer concepts
##      | a               |
##      | attr:name:"Bob" |
##
##    When get answers of typeql read query
##      """
##      match
##      $a isa birth-info;
##      """
##    Then answer size is: 0
##
##    Then typeql read query; fails with a message containing: "empty-set for some variable"
##      """
##      match
##      $a isa! valueless-name;
##      """
##    When transaction closes
##
##    When connection open write transaction for database: typedb
##    Then typeql read query; fails with a message containing: "empty-set for some variable"
##      """
##      match
##      $a isa! birth-info;
##      """
##
##  #######################
##  # ATTRIBUTE OWNERSHIP #
##  #######################
##
##  Scenario: 'has' can be used to match things that own any instance of the specified attribute
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Leila", has ref 0;
##      $y isa person, has ref 1;
##      $c isa company, has name "TypeDB", has ref 2;
##      $d isa company, has ref 3;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has name $y;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:2 |
##
##
##  Scenario: using the 'attribute' meta label, 'has' can match things that own any attribute with a specified value
##    Given typeql schema query
##      """
##      define
##      attribute shoe-size value integer;
##      person owns shoe-size;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has age 9, has ref 0;
##      $y isa person, has shoe-size 9, has ref 1;
##      $z isa person, has age 12, has shoe-size 12, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has $_ 9;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:1 |
##
##
##  Scenario: when an attribute instance is fully specified, 'has' matches its owners
##    Given typeql schema query
##      """
##      define
##      friendship owns age;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Zoe", has age 21, has ref 0;
##      $y links (friend: $x), isa friendship, has age 21, has ref 1;
##      $w isa person, has ref 2;
##      $v links (friend: $x, friend: $w), isa friendship, has age 7, has ref 3;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has age 21;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:1 |
##
##
##  Scenario: 'has' matches an attribute's owner even if it owns more attributes of the same type
##    Given typeql schema query
##      """
##      define
##      attribute lucky-number value integer;
##      person owns lucky-number @card(0..);
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has lucky-number 10, has lucky-number 20, has lucky-number 30, has ref 0;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has lucky-number 20;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##
##  Scenario: an error is thrown when matching by attribute ownership, when the owned thing is actually an entity
##    Then typeql read query; fails
##      """
##      match $x has person "Luke";
##      """
##    Then transaction is open: true
##
##
##  Scenario: exception is thrown when matching by an attribute ownership, if the owner can't actually own it
##    Then typeql read query; fails
##      """
##      match $x isa company, has age $n;
##      """
##    Then transaction is open: true
##
##
##  Scenario: an error is thrown when matching by attribute ownership, when the owned type label doesn't exist
##    Then typeql read query; fails
##      """
##      match $x has bananananananana "rama";
##      """
##    Then transaction is open: true
##
##
##  Scenario: All instances of the matched attributes that an owner has are returned
##    Given transaction commits
##
##    Given connection open schema transaction for database: typedb
##    Given typeql schema query
##      """
##      define
##      attribute first-name sub name;
##      attribute second-name sub name;
##      attribute passport-first-name sub first-name;
##      person owns first-name @card(0..2), owns second-name, owns passport-first-name;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person,
##        has name "Allie Morgan",
##        has first-name "Allie",
##        has second-name "Morgan",
##        has passport-first-name "Alice",
##        has ref 0;
##      """
##    Given transaction commits
##    Given connection open read transaction for database: typedb
##
##    When get answers of typeql read query
##      """
##      match $_ has $a;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:ref:0                       |
##      | attr:name:"Allie Morgan"         |
##      | attr:first-name:"Allie"          |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $_ has name $a;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:name:"Allie Morgan"         |
##      | attr:first-name:"Allie"          |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $_ has first-name $a;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:first-name:"Allie"          |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $_ has second-name $a;
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match $_ has passport-first-name $a;
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match
##      $_ has name $a;
##      not { $a isa! passport-first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:name:"Allie Morgan"  |
##      | attr:first-name:"Allie"   |
##      | attr:second-name:"Morgan" |
##
##    When get answers of typeql read query
##      """
##      match $_ has name $a;
##      not { $a isa! first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                                |
##      | attr:name:"Allie Morgan"         |
##      | attr:second-name:"Morgan"        |
##      | attr:passport-first-name:"Alice" |
##
##    When get answers of typeql read query
##      """
##      match $_ has name $a;
##      not { $a isa first-name; };
##      """
##    Then uniquely identify answer concepts
##      | a                         |
##      | attr:name:"Allie Morgan"  |
##      | attr:second-name:"Morgan" |
##
##  ##############################
##  # ATTRIBUTE VALUE COMPARISON #
##  ##############################
##
##  Scenario: when things own attributes of different types but the same value, they match by equality
##    Given typeql schema query
##      """
##      define
##      attribute start-date value date;
##      attribute graduation-date value date;
##      person owns graduation-date;
##      employment owns start-date;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "James", has ref 0, has graduation-date 2009-07-16;
##      $r links (employee: $x), isa employment, has start-date 2009-07-16, has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Then get answers of typeql read query
##      """
##      match
##        $x isa person, has graduation-date $date;
##        $r links (employee: $x), isa employment, has start-date == $date;
##      """
##    Then answer size is: 1
##    Then uniquely identify answer concepts
##      | x         | r         | date                            |
##      | key:ref:0 | key:ref:1 | attr:graduation-date:2009-07-16 |
##
##
##  Scenario: 'has $attr == $x' matches owners of any instance '$y' of '$attr' where '$y' and '$x' are equal by value
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Susie", has age 16, has ref 0;
##      $y isa person, has name "Donald", has age 25, has ref 1;
##      $z isa person, has name "Ralph", has age 18, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has age == 16;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##
##  Scenario: 'has $attr > $x' matches owners of any instance '$y' of '$attr' where '$y > $x'
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Susie", has age 16, has ref 0;
##      $y isa person, has name "Donald", has age 25, has ref 1;
##      $z isa person, has name "Ralph", has age 18, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has age > 18;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:1 |
##
##
##  Scenario: 'has $attr < $x' matches owners of any instance '$y' of '$attr' where '$y < $x'
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Susie", has age 16, has ref 0;
##      $y isa person, has name "Donald", has age 25, has ref 1;
##      $z isa person, has name "Ralph", has age 18, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has age < 18;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##
##  Scenario: 'has $attr != $x' matches owners of any instance '$y' of '$attr' where '$y != $x'
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Susie", has age 16, has ref 0;
##      $y isa person, has name "Donald", has age 25, has ref 1;
##      $z isa person, has name "Ralph", has age 18, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has age != 18;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:1 |
##
##
##  Scenario: value comparisons can be performed between a 'double' and a 'integer'
##    Given typeql schema query
##      """
##      define
##      attribute house-number @independent, value integer;
##      attribute length @independent, value double;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa house-number 1;
##      $y isa length 2.0;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        $x isa house-number;
##        $x == 1.0;
##      """
##    Then answer size is: 1
##    When get answers of typeql read query
##      """
##      match
##        $x isa length;
##        $x == 2;
##      """
##    Then answer size is: 1
##    When get answers of typeql read query
##      """
##      match
##        $x isa house-number;
##        $x == 1.0;
##      """
##    Then answer size is: 1
##    When get answers of typeql read query
##      """
##      match
##        $x isa length;
##        $x == 2;
##      """
##    Then answer size is: 1
##    When get answers of typeql read query
##      """
##      match
##        $x isa $a;
##        $x >= 1;
##      """
##    Then answer size is: 2
##    When get answers of typeql read query
##      """
##      match
##        $x isa $a;
##        $x < 2.0;
##      """
##    Then answer size is: 1
##
##    When get answers of typeql read query
##      """
##      match
##        $x isa house-number;
##        $y isa length;
##        $x < $y;
##      """
##    Then answer size is: 1
##
##
##  Scenario: when a thing owns multiple attributes of the same type, a value comparison matches if any value matches
##    Given typeql schema query
##      """
##      define
##      attribute lucky-number value integer;
##      person owns lucky-number @card(0..);
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has lucky-number 10, has lucky-number 20, has lucky-number 30, has ref 0;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x has lucky-number > 25;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##
##  Scenario: an attribute variable used in both '=' and '>=' predicates is correctly resolved
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Susie", has age 16, has ref 0;
##      $y isa person, has name "Donald", has age 25, has ref 1;
##      $z isa person, has name "Ralph", has age 18, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        $x has age == $z;
##        $z >= 17;
##        $z isa age;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:1 |
##      | key:ref:2 |
##
##
##  Scenario: when the answers of a value comparison include both a 'double' and a 'integer', both answers are returned
##    Given typeql schema query
##      """
##      define
##      attribute length @independent, value double;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $a isa age 24;
##      $b isa age 19;
##      $c isa length 20.9;
##      $d isa length 19.9;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        $x isa $_;
##        $x > 20;
##      """
##    Then uniquely identify answer concepts
##      | x                |
##      | attr:age:24      |
##      | attr:length:20.9 |
##
##
##  Scenario: when one entity exists, and we match two variables with concept inequality, an empty answer is returned
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert $x isa person, has ref 0;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        $x isa person;
##        $y isa person;
##        not { $x is $y; };
##      """
##    Then answer size is: 0
##
##
##  Scenario: concept comparison of unbound variables throws an error
##    Then typeql read query; fails
##      """
##      match $x is $y;
##      """
##    Then transaction is open: true
##
##  ############
##  # PATTERNS #
##  ############
##
##  Scenario: disjunctions return the union of composing query statements
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Jeff", has ref 0;
##      $y isa company, has name "Amazon", has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x isa $t; { $t label person; } or { $t label company; };
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:1 |
##    When get answers of typeql read query
##      """
##      match $x isa $_; { $x has name "Jeff"; } or { $x has name "Amazon"; };
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##      | key:ref:1 |
##
##
##  Scenario: disjunctions with no answers can be limited
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x isa $t; { $t label person; } or { $t label company; };
##      """
##    Then answer size is: 0
##
##
##  Scenario: a variable can be reused across disjunction branches
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##        $first isa person, has ref 0;
##        $second isa person, has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match { $person isa person, has ref 0; } or { $person isa person, has ref 1; };
##      """
##    Then uniquely identify answer concepts
##      | person    |
##      | key:ref:0 |
##      | key:ref:1 |
##
##
##  Scenario: a disjunction that both binds and consumes a variable can be planned
##    Given typeql write query
##      """
##      insert
##        $_ isa person, has ref 0;
##        $_ isa person, has ref 1;
##        $_ isa person, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Then get answers of typeql read query
##      """
##      with fun refof($x:person) -> { ref }: match $x isa person; $_ has ref $ref; return { $ref };
##      match $x has ref $ref; { let $b = $ref; } or { let $ref in refof($x); };
##      """
##    Then uniquely identify answer concepts
##      | x         | ref        |
##      | key:ref:0 | attr:ref:0 |
##      | key:ref:1 | attr:ref:1 |
##      | key:ref:2 | attr:ref:2 |
##
##
##  Scenario: negations can be applied to filtered variables
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Jeff", has ref 0;
##      $y isa person, has name "Jenny", has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match $x isa person, has name $a; not { $a == "Jeff"; };
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:1 |
##
##
##  Scenario: multiple negations can be applied
##    Given typeql schema query
##      """
##      define
##        entity direction;
##        entity east sub direction;
##        entity west sub direction;
##        entity north sub direction;
##        entity south sub direction;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    When get answers of typeql read query
##      """
##      match
##        $x sub! direction;
##        not { $x label east; };
##        not { $x label west; };
##        not { $x label south; };
##      """
##    Then uniquely identify answer concepts
##      | x           |
##      | label:north |
##
##  Scenario: pattern variable without named variable is invalid
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Then typeql read query; parsing fails
##      """
##      match $x isa person, has name $a; "bob" isa name;
##      """
##
##
##  ##################
##  # VARIABLE TYPES #
##  ##################
##
##  Scenario: all instances and their types can be retrieved
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has name "Bertie", has ref 0;
##      $y isa person, has name "Angelina", has ref 1;
##      $r links (friend: $x, friend: $y), isa friendship, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match entity $t; $x isa $t;
##      """
##    Given answer size is: 2
##    Given get answers of typeql read query
##      """
##      match relation $t; $x isa $t;
##      """
##    Given answer size is: 1
##    Given get answers of typeql read query
##      """
##      match attribute $t; $x isa $t;
##      """
##    Given answer size is: 5
##    When get answers of typeql read query
##      """
##      match $x isa $type;
##      """
##    # 2 entities x 1 type {person}
##    # 1 relation x 1 type {friendship}
##    # 5 attributes x 1 type {ref/name}
##    Then answer size is: 8
##
##
##  Scenario: all relations and their types can be retrieved
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##       $x isa person, has name "Bertie", has ref 0;
##       $y isa person, has name "Angelina", has ref 1;
##       $r links (friend: $x, friend: $y), isa friendship, has ref 2;
##       """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##       """
##       match relation $t; $r isa $t;
##       """
##    Given answer size is: 1
##    Given get answers of typeql read query
##       """
##       match ($x, $y);
##       """
##     # 2 permutations of the roleplayers
##    Given answer size is: 2
##    When get answers of typeql read query
##       """
##       match ($x, $y) isa $type;
##       """
##     # 2 permutations of the roleplayers
##    Then answer size is: 2
##
##
##  Scenario: variable role types with relations playing roles
##    Given typeql schema query
##       """
##       define
##         relation parent relates nested, owns id;
##         relation nested relates player, plays parent:nested;
##         entity player owns id, plays nested:player;
##         attribute id value string;
##       """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert
##         $i1 isa id "i1";
##         $i2 isa id "i2";
##         $pl1 isa player, has id $i1;
##         $pl2 isa player, has id $i2;
##         $n1 isa nested, links (player: $pl1);
##         $n2 isa nested, links (player: $pl2);
##         $par1 isa parent, links (nested: $n1), has id $i1;
##         $par2 isa parent, links (nested: $n2), has id $i2;
##       """
##    Given transaction commits
##    Given connection open read transaction for database: typedb
##
##     # Force traversal of role edges in each direction: See typedb/typedb#6925
##    When get answers of typeql read query
##       """
##       match
##         let $boundId1 = "i1";
##
##         $p links ($role-nested: $n), isa parent, has id == $boundId1;
##         $n links ($role-player: $i), isa nested;
##
##         not { $role-nested sub! $r1; };
##         not { $role-player sub! $r2; };
##       """
##    Then answer size is: 1
##
##    When get answers of typeql read query
##       """
##       match
##         let $boundId1 = "i1";
##
##         $r links ($role-nested: $n), isa parent, has id $i;
##         $n links ($role-player: $p), isa nested;
##         $p has $pid;
##         $pid == $boundId1;
##
##         not { $role-nested sub! $r1; };
##         not { $role-player sub! $r2; };
##       """
##    Then answer size is: 1
##
##
##  #######################
##  # NEGATION VALIDATION #
##  #######################
##
##  # TODO: Do we want to allow this? Or WARN?
##  Scenario: the entire match clause may be a negation
##  At least one negated pattern variable must be bound outside the negation block, so this query is invalid.
##    Then typeql read query
##       """
##       match not { $x has $a "value"; };
##       """
##
##
##   # TODO: 3.x: Do we want to disable this? Or WARN?
##  Scenario: matching a negation whose pattern variables are all unbound outside it is allowed
##    Then typeql read query
##       """
##       match
##         entity $t;
##         $r isa $t;
##         not {
##           $r0 links ($r2, $i);
##         };
##       """
##
##
##  Scenario: the first variable in a negation can be unbound, as integer as it is connected to a bound variable
##    Then get answers of typeql read query
##      """
##      match
##        attribute $a;
##        $r isa $a;
##        not {
##          $x has $r;
##        };
##      """
##
##
##   # TODO: 3.x: The original test was to check this was disallowed. Do we want to disallow it? Or WARN?
##  Scenario: negating a negation redundantly is allowed
##    Given transaction closes
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##       """
##       insert $x isa person, has name "Tim", has age 55, has ref 0;
##       """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Then get answers of typeql read query
##       """
##       match
##         $x isa person, has name "Tim";
##         not {
##           not {
##             $x has age 55;
##           };
##         };
##       """
##    Then answer size is: 1
##
##    Then get answers of typeql read query
##       """
##       match
##         $x isa person, has name "Tim";
##         not {
##           not {
##             $x has age 50;
##           };
##         };
##       """
##    Then answer size is: 0
##
##
##  #######################
##  #   Unicode Support   #
##  #######################
##
##  Scenario: string attribute values can be non-ascii
##    Given typeql schema query
##      """
##      define
##      person owns favorite-phrase;
##      attribute favorite-phrase value string;
##      """
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa person, has favorite-phrase "你明白了吗", has ref 0;
##      $y isa person, has favorite-phrase "בוקר טוב", has ref 1;
##      $r links (friend: $x, friend: $y), isa friendship, has ref 2;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match $phrase isa favorite-phrase;
##      """
##    Then uniquely identify answer concepts
##      | phrase                        |
##      | attr:favorite-phrase:你明白了吗    |
##      | attr:favorite-phrase:בוקר טוב |
##
##    Given get answers of typeql read query
##      """
##      match $x isa person, has favorite-phrase "你明白了吗";
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##    Given get answers of typeql read query
##      """
##      match $x isa person, has favorite-phrase "בוקר טוב";
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:1 |
##
##    Given get answers of typeql read query
##      """
##      match $x isa person, has favorite-phrase "请给我一";
##      """
##    Then answer size is: 0
##
##
##  Scenario: type labels can be non-ascii
##    Given typeql schema query
##      """
##      define
##      entity 人 owns name, owns ref @key; entity אדם owns name, owns ref @key;
##      """
##    Given transaction commits
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $x isa 人, has name "Liu", has ref 0;
##      $y isa אדם, has name "Solomon", has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match $x isa! $t; $x has name $_;
##      """
##    Then uniquely identify answer concepts
##      | t         |
##      | label:人   |
##      | label:אדם |
##
##    Given get answers of typeql read query
##      """
##      match $x isa 人;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:0 |
##
##    Given get answers of typeql read query
##      """
##      match $x isa אדם;
##      """
##    Then uniquely identify answer concepts
##      | x         |
##      | key:ref:1 |
##
##
##  Scenario: variables can be non-ascii
##    Given transaction commits
##
##    Given connection open write transaction for database: typedb
##    Given typeql write query
##      """
##      insert
##      $人 isa person, has name "Liu", has ref 0;
##      $אדם isa person, has name "Solomon", has ref 1;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match $人 isa person; $人 has name "Liu";
##      """
##    Then uniquely identify answer concepts
##      | 人         |
##      | key:ref:0 |
##
##    Given get answers of typeql read query
##      """
##      match $אדם isa person; $אדם has name "Solomon";
##      """
##    Then uniquely identify answer concepts
##      | אדם       |
##      | key:ref:1 |
##
##
##  Scenario: labels and variables have different identifier formats
##    Given typeql schema query; parsing fails
##      """
##      define
##      entity 0_leading_digit_fails;
##      """
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match
##      entity $0_leading_digit_allowed;
##      """
##    Given transaction closes
##
##    Given connection open schema transaction for database: typedb
##    Given typeql schema query; parsing fails
##      """
##      define
##      entity _leading_connector_disallowed;
##      """
##
##    Given connection open read transaction for database: typedb
##    Given typeql read query; parsing fails
##      """
##      match
##      entity $_leading_connector_disallowed;
##      """
##
##    Given connection open schema transaction for database: typedb
##    Given typeql schema query
##      """
##      define
##      entity following_connectors-and-digits-1-2-3-allowed;
##      """
##    Given transaction commits
##
##    Given connection open read transaction for database: typedb
##    Given get answers of typeql read query
##      """
##      match
##      entity $following_connectors-and-digits-1-2-3-allowed;
##      """
