# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

$ set-arg-default default-storage-size=1

$ postgres-execute connection=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}
ALTER SYSTEM SET max_clusters = 20

# Regression test for https://github.com/MaterializeInc/database-issues/issues/3135
#
# This file uses the old create source syntax.

$ set-sql-timeout duration=300s

$ set keyschema={"type": "record", "name": "Key", "fields": [ { "name": "f1", "type": "long" } ] }

$ set schema={"type" : "record", "name" : "test", "fields": [ { "name": "f2", "type": "long" } ] }

$ set count=100000

# Create sources and fill them with data and render one dataflow that uses everything just to
# stress the system.

$ kafka-create-topic topic=multi-topic-0

$ kafka-ingest format=avro topic=multi-topic-0 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-1

$ kafka-ingest format=avro topic=multi-topic-1 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-2

$ kafka-ingest format=avro topic=multi-topic-2 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-3

$ kafka-ingest format=avro topic=multi-topic-3 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-4

$ kafka-ingest format=avro topic=multi-topic-4 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-5

$ kafka-ingest format=avro topic=multi-topic-5 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-6

$ kafka-ingest format=avro topic=multi-topic-6 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-7

$ kafka-ingest format=avro topic=multi-topic-7 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-8

$ kafka-ingest format=avro topic=multi-topic-8 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

$ kafka-create-topic topic=multi-topic-9

$ kafka-ingest format=avro topic=multi-topic-9 schema=${schema} repeat=${count}
{"f2": ${kafka-ingest.iteration} }

> CREATE CONNECTION IF NOT EXISTS csr_conn TO CONFLUENT SCHEMA REGISTRY (
    URL '${testdrive.schema-registry-url}'
  );

> CREATE CONNECTION IF NOT EXISTS kafka_conn TO KAFKA (BROKER '${testdrive.kafka-addr}', SECURITY PROTOCOL PLAINTEXT);

> CREATE CLUSTER s0_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s0 IN CLUSTER s0_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-0-${testdrive.seed}');

> CREATE TABLE s0_tbl FROM SOURCE s0 (REFERENCE "testdrive-multi-topic-0-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s1_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s1 IN CLUSTER s1_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-1-${testdrive.seed}');

> CREATE TABLE s1_tbl FROM SOURCE s1 (REFERENCE "testdrive-multi-topic-1-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s2_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s2 IN CLUSTER s2_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-2-${testdrive.seed}');

> CREATE TABLE s2_tbl FROM SOURCE s2 (REFERENCE "testdrive-multi-topic-2-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s3_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s3 IN CLUSTER s3_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-3-${testdrive.seed}');

> CREATE TABLE s3_tbl FROM SOURCE s3 (REFERENCE "testdrive-multi-topic-3-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s4_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s4 IN CLUSTER s4_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-4-${testdrive.seed}');

> CREATE TABLE s4_tbl FROM SOURCE s4 (REFERENCE "testdrive-multi-topic-4-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s5_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s5 IN CLUSTER s5_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-5-${testdrive.seed}');

> CREATE TABLE s5_tbl FROM SOURCE s5 (REFERENCE "testdrive-multi-topic-5-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s6_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s6 IN CLUSTER s6_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-6-${testdrive.seed}');

> CREATE TABLE s6_tbl FROM SOURCE s6 (REFERENCE "testdrive-multi-topic-6-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s7_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s7 IN CLUSTER s7_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-7-${testdrive.seed}');

> CREATE TABLE s7_tbl FROM SOURCE s7 (REFERENCE "testdrive-multi-topic-7-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s8_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s8 IN CLUSTER s8_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-8-${testdrive.seed}');

> CREATE TABLE s8_tbl FROM SOURCE s8 (REFERENCE "testdrive-multi-topic-8-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE CLUSTER s9_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE s9 IN CLUSTER s9_cluster
  FROM KAFKA CONNECTION kafka_conn
  (TOPIC 'testdrive-multi-topic-9-${testdrive.seed}');

> CREATE TABLE s9_tbl FROM SOURCE s9 (REFERENCE "testdrive-multi-topic-9-${testdrive.seed}")
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn ENVELOPE NONE;

> CREATE MATERIALIZED VIEW v1 AS
  SELECT SUM(f1) AS f1 FROM
  (SELECT
    COUNT(*) AS f1 FROM s0_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s1_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s2_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s3_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s4_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s5_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s6_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s7_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s8_tbl
      UNION ALL SELECT COUNT(*) AS f1 FROM s9_tbl);

# Make sure that s1 has been fully timestamped
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

# Now disable retries, and verify that we get the exact same result multiple times
# in a row. Obviously, this test will not always catch the issue since the original
# bug was nondeterministic, but this is a good best-effort smake test.

$ set-max-tries max-tries=1

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000

> SELECT mz_unsafe.mz_sleep(0.2);
<null>
> SELECT COUNT(*) FROM s1_tbl AS OF AT LEAST 0;
count
-----
100000
