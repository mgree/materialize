# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

$ postgres-execute connection=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}
ALTER SYSTEM SET unsafe_enable_unorchestrated_cluster_replicas = true

> CREATE CLUSTER cluster1 REPLICAS (r1 (SIZE '2'))

> CREATE CONNECTION kafka_conn
  TO KAFKA (BROKER '${testdrive.kafka-addr}', SECURITY PROTOCOL PLAINTEXT);

> CREATE TABLE t (a text, b text)
> CREATE MATERIALIZED VIEW simple_view AS SELECT * from t;
> INSERT INTO t VALUES ('key1', 'value')

# Setup various sinks and sources
> CREATE CLUSTER sink_size_cluster SIZE '2';
> CREATE SINK sink_size
  IN CLUSTER sink_size_cluster
  FROM simple_view
  INTO KAFKA CONNECTION kafka_conn (TOPIC 'topic-${testdrive.seed}')
  KEY (a)
  FORMAT JSON
  ENVELOPE DEBEZIUM

> CREATE SINK sink_cluster
  IN CLUSTER cluster1
  FROM simple_view
  INTO KAFKA CONNECTION kafka_conn (TOPIC 'topic-${testdrive.seed}')
  KEY (a)
  FORMAT JSON
  ENVELOPE DEBEZIUM

$ kafka-create-topic topic=upsert partitions=1
$ kafka-ingest format=bytes topic=upsert key-format=bytes key-terminator=:
one:two

> CREATE CLUSTER upsert_size_cluster SIZE '2';
> CREATE SOURCE upsert_size
  IN CLUSTER upsert_size_cluster
  FROM KAFKA CONNECTION kafka_conn (TOPIC
  'testdrive-upsert-${testdrive.seed}'
  )
  KEY FORMAT BYTES
  VALUE FORMAT BYTES
  ENVELOPE UPSERT

> CREATE SOURCE upsert_cluster
  IN CLUSTER cluster1
  FROM KAFKA CONNECTION kafka_conn (TOPIC
  'testdrive-upsert-${testdrive.seed}'
  )
  KEY FORMAT BYTES
  VALUE FORMAT BYTES
  ENVELOPE UPSERT

> CREATE SCHEMA subsources_size;
> CREATE SCHEMA subsources_cluster;
> CREATE CLUSTER subsource_size_s_cluster SIZE '2';
> CREATE SOURCE subsources_size.s IN CLUSTER subsource_size_s_cluster FROM LOAD GENERATOR AUCTION (UP TO 100);
> CREATE SOURCE subsources_cluster.s IN CLUSTER cluster1 FROM LOAD GENERATOR AUCTION (UP TO 100);

> CREATE TABLE subsources_size.accounts FROM SOURCE subsources_size.s (REFERENCE accounts);
> CREATE TABLE subsources_size.auctions FROM SOURCE subsources_size.s (REFERENCE auctions);
> CREATE TABLE subsources_size.bids FROM SOURCE subsources_size.s (REFERENCE bids);
> CREATE TABLE subsources_size.organizations FROM SOURCE subsources_size.s (REFERENCE organizations);
> CREATE TABLE subsources_size.users FROM SOURCE subsources_size.s (REFERENCE users);

> CREATE TABLE subsources_cluster.accounts FROM SOURCE subsources_cluster.s (REFERENCE accounts);
> CREATE TABLE subsources_cluster.auctions FROM SOURCE subsources_cluster.s (REFERENCE auctions);
> CREATE TABLE subsources_cluster.bids FROM SOURCE subsources_cluster.s (REFERENCE bids);
> CREATE TABLE subsources_cluster.organizations FROM SOURCE subsources_cluster.s (REFERENCE organizations);
> CREATE TABLE subsources_cluster.users FROM SOURCE subsources_cluster.s (REFERENCE users);

# NOTE: These queries are slow to succeed because the default metrics scraping
# interval is 30 seconds. Here we are just ensuring metrics were populated.

> SELECT s.name, SUM(u.messages_staged), SUM(u.messages_committed), SUM(u.bytes_staged) > 0, SUM(bytes_staged) = SUM(bytes_committed)
  FROM mz_sinks s
  JOIN mz_internal.mz_sink_statistics_raw u ON s.id = u.id
  WHERE s.name IN ('sink_size', 'sink_cluster')
  GROUP BY s.name
sink_size 1 1 true true
sink_cluster 1 1 true true

> SELECT s.name,
  SUM(u.updates_committed) > 0
  FROM mz_sources s
  JOIN mz_internal.mz_source_statistics_raw u ON s.id = u.id
  WHERE s.name IN ('upsert_size', 'upsert_cluster', 's', 'bids')
  GROUP BY s.id, s.name
upsert_size true
upsert_cluster true
s false
s false

# We have to obtain these before we delete the sink.
$ set-from-sql var=sink-size-id
SELECT s.id
FROM mz_sinks s
WHERE s.name IN ('sink_size')
$ set-from-sql var=sink-cluster-id
SELECT s.id
FROM mz_sinks s
WHERE s.name IN ('sink_cluster')

$ set-from-sql var=upsert-size-id
SELECT s.id
FROM mz_sources s
WHERE s.name IN ('upsert_size')
$ set-from-sql var=upsert-cluster-id
SELECT s.id
FROM mz_sources s
WHERE s.name IN ('upsert_cluster')

# We also need to check that subsources and top-level
# sources are cleared out.
$ set-from-sql var=subsources-size-top-level-id
SELECT s.id
FROM mz_sources s
JOIN mz_schemas sch
ON sch.id = s.schema_id
WHERE s.name IN ('s') AND sch.name = 'subsources_size'
$ set-from-sql var=subsources-size-bids-id
SELECT t.id
FROM mz_tables t
JOIN mz_schemas sch
ON sch.id = t.schema_id
WHERE t.name IN ('bids') AND sch.name = 'subsources_size'

$ set-from-sql var=subsources-cluster-top-level-id
SELECT s.id
FROM mz_sources s
JOIN mz_schemas sch
ON sch.id = s.schema_id
WHERE s.name IN ('s') AND sch.name = 'subsources_cluster'
$ set-from-sql var=subsources-cluster-bids-id
SELECT t.id
FROM mz_tables t
JOIN mz_schemas sch
ON sch.id = t.schema_id
WHERE t.name IN ('bids') AND sch.name = 'subsources_cluster'

> DROP SINK sink_size
> DROP SINK sink_cluster
> DROP SOURCE upsert_size CASCADE
> DROP SOURCE upsert_cluster CASCADE
> DROP SOURCE subsources_size.s CASCADE;
> DROP SOURCE subsources_cluster.s CASCADE;

> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${sink-size-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${sink-cluster-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${upsert-size-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${upsert-cluster-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${subsources-size-top-level-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${subsources-size-bids-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${subsources-cluster-top-level-id}'
0
> SELECT COUNT(*)
  FROM mz_internal.mz_sink_statistics_raw u
  WHERE u.id = '${subsources-cluster-bids-id}'
0
