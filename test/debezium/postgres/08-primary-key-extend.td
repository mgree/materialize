# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

#
# Extend the number of columns that participate in a primary key
# Currently, this throws an error on the Debezium side and replication stops
#

# TODO: Reenable when database-issues#2047 is fixed
$ skip-if
SELECT true

$ postgres-execute connection=postgres://postgres:postgres@postgres
CREATE TABLE alter_extend_primary_key (f1 INTEGER, f2 INTEGER, PRIMARY KEY (f1));
ALTER TABLE alter_extend_primary_key REPLICA IDENTITY FULL;
INSERT INTO alter_extend_primary_key VALUES (123, 234), (345, 456);

> CREATE CONNECTION IF NOT EXISTS csr_conn TO CONFLUENT SCHEMA REGISTRY (
    URL '${testdrive.schema-registry-url}'
  );

> CREATE CONNECTION IF NOT EXISTS kafka_conn TO KAFKA (BROKER '${testdrive.kafka-addr}', SECURITY PROTOCOL PLAINTEXT);

> CREATE SOURCE alter_extend_primary_key
  FROM KAFKA CONNECTION kafka_conn (TOPIC 'postgres.public.alter_extend_primary_key');

> CREATE TABLE alter_extend_primary_key_tbl FROM SOURCE alter_extend_primary_key (REFERENCE "postgres.public.alter_extend_primary_key")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn
  ENVELOPE DEBEZIUM;

> SELECT * FROM alter_extend_primary_key_tbl;
123 234
345 456

$ postgres-execute connection=postgres://postgres:postgres@postgres
ALTER TABLE alter_extend_primary_key DROP CONSTRAINT alter_extend_primary_key_pkey, ADD PRIMARY KEY (f1, f2);
INSERT INTO alter_extend_primary_key VALUES (123, 567);
DELETE FROM alter_extend_primary_key WHERE f1 = 345;

# The updates after the ALTER TABLE are not replicated as replication has stopped
> SELECT * FROM alter_extend_primary_key_tbl;
123 234
345 456
