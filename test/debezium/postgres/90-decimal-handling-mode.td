# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

#
# Start with decimal.handling.mode PRECISE
#

$ postgres-execute connection=postgres://postgres:postgres@postgres
CREATE TABLE decimal_handling_mode_precise (f1 DECIMAL(10,3) PRIMARY KEY);
INSERT INTO decimal_handling_mode_precise VALUES (1234567.890);

$ schema-registry-wait topic=postgres.public.decimal_handling_mode_precise

> CREATE CONNECTION IF NOT EXISTS csr_conn TO CONFLUENT SCHEMA REGISTRY (
    URL '${testdrive.schema-registry-url}'
  );

> CREATE CONNECTION IF NOT EXISTS kafka_conn TO KAFKA (BROKER '${testdrive.kafka-addr}', SECURITY PROTOCOL PLAINTEXT);

> CREATE SOURCE decimal_handling_mode_precise
  FROM KAFKA CONNECTION kafka_conn (TOPIC 'postgres.public.decimal_handling_mode_precise');

> CREATE TABLE decimal_handling_mode_precise_tbl FROM SOURCE decimal_handling_mode_precise (REFERENCE "postgres.public.decimal_handling_mode_precise")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn
  ENVELOPE DEBEZIUM;

> SELECT f1, pg_typeof(f1) FROM decimal_handling_mode_precise_tbl
1234567.89 numeric

#
# Set decimal.handling.mode to DOUBLE
#

$ http-request method=PUT url=http://debezium:8083/connectors/psql-connector/config content-type=application/json
{
  "connector.class": "io.debezium.connector.postgresql.PostgresConnector",
  "database.hostname": "postgres",
  "database.port": "5432",
  "database.user": "debezium",
  "database.password": "debezium",
  "database.dbname" : "postgres",
  "database.server.name": "postgres",
  "plugin.name": "pgoutput",
  "slot.name" : "tester",
  "database.history.kafka.bootstrap.servers": "kafka:9092",
  "database.history.kafka.topic": "schema-changes.history",
  "truncate.handling.mode": "include",
  "decimal.handling.mode": "double",
  "topic.prefix": "postgres"
}

# PUT requests do not take effect immediately, we need to sleep

$ sleep-is-probably-flaky-i-have-justified-my-need-with-a-comment duration="10s"

$ postgres-execute connection=postgres://postgres:postgres@postgres
CREATE TABLE decimal_handling_mode_double (f1 DECIMAL(10,3) PRIMARY KEY);
INSERT INTO decimal_handling_mode_double VALUES (2234567.890);

$ schema-registry-wait topic=postgres.public.decimal_handling_mode_double

> CREATE SOURCE decimal_handling_mode_double
  FROM KAFKA CONNECTION kafka_conn (TOPIC 'postgres.public.decimal_handling_mode_double');

> CREATE TABLE decimal_handling_mode_double_tbl FROM SOURCE decimal_handling_mode_double (REFERENCE "postgres.public.decimal_handling_mode_double")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn
  ENVELOPE DEBEZIUM;

> SELECT f1, pg_typeof(f1) FROM decimal_handling_mode_double_tbl;
2234567.89 "double precision"

#
# Set decimal.handling.mode to STRING
#

$ http-request method=PUT url=http://debezium:8083/connectors/psql-connector/config content-type=application/json
{
  "connector.class": "io.debezium.connector.postgresql.PostgresConnector",
  "database.hostname": "postgres",
  "database.port": "5432",
  "database.user": "debezium",
  "database.password": "debezium",
  "database.dbname" : "postgres",
  "database.server.name": "postgres",
  "plugin.name": "pgoutput",
  "slot.name" : "tester",
  "database.history.kafka.bootstrap.servers": "kafka:9092",
  "database.history.kafka.topic": "schema-changes.history",
  "truncate.handling.mode": "include",
  "provide.transaction.metadata": "true",
  "decimal.handling.mode": "string",
  "topic.prefix": "postgres"
}

$ sleep-is-probably-flaky-i-have-justified-my-need-with-a-comment duration="10s"

$ postgres-execute connection=postgres://postgres:postgres@postgres
CREATE TABLE decimal_handling_mode_string (f1 DECIMAL(10,3) PRIMARY KEY);
INSERT INTO decimal_handling_mode_string VALUES (3234567.890);

$ schema-registry-wait topic=postgres.public.decimal_handling_mode_string

> CREATE SOURCE decimal_handling_mode_string
  FROM KAFKA CONNECTION kafka_conn (TOPIC 'postgres.public.decimal_handling_mode_string');

> CREATE TABLE decimal_handling_mode_string_tbl FROM SOURCE decimal_handling_mode_string (REFERENCE "postgres.public.decimal_handling_mode_string")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn
  ENVELOPE DEBEZIUM;

> SELECT f1, pg_typeof(f1) FROM decimal_handling_mode_string_tbl;
3234567.890 text

#
# Restore default
#

$ http-request method=PUT url=http://debezium:8083/connectors/psql-connector/config content-type=application/json
{
  "connector.class": "io.debezium.connector.postgresql.PostgresConnector",
  "database.hostname": "postgres",
  "database.port": "5432",
  "database.user": "debezium",
  "database.password": "debezium",
  "database.dbname" : "postgres",
  "database.server.name": "postgres",
  "plugin.name": "pgoutput",
  "slot.name" : "tester",
  "database.history.kafka.bootstrap.servers": "kafka:9092",
  "database.history.kafka.topic": "schema-changes.history",
  "truncate.handling.mode": "include",
  "decimal.handling.mode": "precise",
  "topic.prefix": "postgres"
}

$ sleep-is-probably-flaky-i-have-justified-my-need-with-a-comment duration="10s"
