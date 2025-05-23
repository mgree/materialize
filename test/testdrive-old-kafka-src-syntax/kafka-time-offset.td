# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

$ set-arg-default default-storage-size=1
$ set-arg-default single-replica-cluster=quickstart

$ postgres-execute connection=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}
ALTER SYSTEM SET max_clusters = 20

# Tests for `START TIMESTAMP` configuration which resolves a start offset
# during creation of the source.

#
# Errors
#

$ kafka-create-topic topic=t0

> CREATE CONNECTION kafka_conn
  TO KAFKA (BROKER '${testdrive.kafka-addr}', SECURITY PROTOCOL PLAINTEXT);

> CREATE CONNECTION IF NOT EXISTS csr_conn TO CONFLUENT SCHEMA REGISTRY (
    URL '${testdrive.schema-registry-url}'
  );

! CREATE SOURCE missing_topic
  IN CLUSTER ${arg.single-replica-cluster}
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=1, TOPIC 'missing_topic')
  FORMAT TEXT
  INCLUDE OFFSET
contains:Topic does not exist

! CREATE SOURCE pick_one
  IN CLUSTER ${arg.single-replica-cluster}
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=1, START OFFSET=[1], TOPIC 'testdrive-t0-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET
contains:cannot specify START TIMESTAMP and START OFFSET at same time


! CREATE SOURCE not_a_number
  IN CLUSTER ${arg.single-replica-cluster}
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP="not_a_number", TOPIC 'testdrive-t0-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET
contains:invalid START TIMESTAMP: cannot use value as number

#
# Append-Only
#

$ kafka-create-topic topic=t1 partitions=3

$ kafka-ingest format=bytes topic=t1 key-format=bytes key-terminator=: timestamp=1 partition=0
apple:apple
banana:banana

$ kafka-ingest format=bytes topic=t1 key-format=bytes key-terminator=: timestamp=2 partition=1
cherry:cherry
date:date
eggfruit:eggfruit

$ kafka-ingest format=bytes topic=t1 key-format=bytes key-terminator=: timestamp=3 partition=1
fig:fig

$ kafka-ingest format=bytes topic=t1 key-format=bytes key-terminator=: timestamp=4 partition=2
grape:grape

> CREATE CLUSTER append_time_offset_0_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_0
  IN CLUSTER append_time_offset_0_cluster
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=0, TOPIC 'testdrive-t1-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER append_time_offset_1_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_1
  IN CLUSTER append_time_offset_1_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=1,
      TOPIC 'testdrive-t1-${testdrive.seed}'
    )
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER append_time_offset_2_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_2
  IN CLUSTER append_time_offset_2_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=2,
      TOPIC 'testdrive-t1-${testdrive.seed}'
    )
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER append_time_offset_3_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_3
  IN CLUSTER append_time_offset_3_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=3,
      TOPIC 'testdrive-t1-${testdrive.seed}'
    )
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER append_time_offset_4_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_4
  IN CLUSTER append_time_offset_4_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=4,
      TOPIC 'testdrive-t1-${testdrive.seed}'
    )
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER append_time_offset_5_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE append_time_offset_5
  IN CLUSTER append_time_offset_5_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=5,
      TOPIC 'testdrive-t1-${testdrive.seed}'
    )
  FORMAT TEXT
  INCLUDE OFFSET

> SELECT * FROM append_time_offset_0
text      offset
-------------------
apple     0
banana    1
cherry    0
date      1
eggfruit  2
fig       3
grape     0

> SELECT * FROM append_time_offset_1
text      offset
-------------------
apple     0
banana    1
cherry    0
date      1
eggfruit  2
fig       3
grape     0

> SELECT * FROM append_time_offset_2
text      offset
-------------------
cherry    0
date      1
eggfruit  2
fig       3
grape     0

> SELECT * FROM append_time_offset_3
text      offset
-------------------
fig       3
grape     0

> SELECT * FROM append_time_offset_4
text      offset
-------------------
grape     0

> SELECT * FROM append_time_offset_5
text      offset
-------------------

$ kafka-add-partitions topic=t1 total-partitions=4

$ kafka-ingest format=bytes topic=t1 key-format=bytes key-terminator=: timestamp=5 partition=3
hazelnut:hazelnut

$ set-sql-timeout duration=60s

> SELECT * FROM append_time_offset_5
text      offset
-------------------
hazelnut  0

#
# Upsert
#

$ kafka-create-topic topic=t2 partitions=3

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=1 partition=0
apple:apple
banana:banana

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=1 partition=0
apple:

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=2 partition=1
cherry:cherry
date:date
eggfruit:eggfruit

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=3 partition=1
cherry:
fig:fig

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=4 partition=2
grape:grape

> CREATE CLUSTER upsert_time_offset_0_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_0
  IN CLUSTER upsert_time_offset_0_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP=0,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> CREATE CLUSTER upsert_time_offset_1_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_1
  IN CLUSTER upsert_time_offset_1_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP 1,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> CREATE CLUSTER upsert_time_offset_2_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_2
  IN CLUSTER upsert_time_offset_2_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP 2,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> CREATE CLUSTER upsert_time_offset_3_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_3
  IN CLUSTER upsert_time_offset_3_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP 3,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> CREATE CLUSTER upsert_time_offset_4_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_4
  IN CLUSTER upsert_time_offset_4_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP 4,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> CREATE CLUSTER upsert_time_offset_5_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_offset_5
  IN CLUSTER upsert_time_offset_5_cluster
  FROM KAFKA CONNECTION kafka_conn (
      START TIMESTAMP 5,
      TOPIC 'testdrive-t2-${testdrive.seed}'
  )
  KEY FORMAT TEXT VALUE FORMAT TEXT
  INCLUDE OFFSET
  ENVELOPE UPSERT

> SELECT * FROM upsert_time_offset_0
key       text      offset
-----------------------------
banana    banana    1
date      date      1
eggfruit  eggfruit  2
fig       fig       4
grape     grape     0

> SELECT * FROM upsert_time_offset_1
key       text      offset
-----------------------------
banana    banana    1
date      date      1
eggfruit  eggfruit  2
fig       fig       4
grape     grape     0

> SELECT * FROM upsert_time_offset_2
key       text      offset
-----------------------------
date      date      1
eggfruit  eggfruit  2
fig       fig       4
grape     grape     0

> SELECT * FROM upsert_time_offset_3
key       text      offset
-----------------------------
fig       fig       4
grape     grape     0

> SELECT * FROM upsert_time_offset_4
key       text      offset
-----------------------------
grape     grape     0

> SELECT * FROM upsert_time_offset_5
key       text      offset
-----------------------------

$ kafka-add-partitions topic=t2 total-partitions=4

$ kafka-ingest format=bytes topic=t2 key-format=bytes key-terminator=: timestamp=5 partition=3
hazelnut:hazelnut

# It takes a while for new partitions to be consumed...
$ set-sql-timeout duration=60s

> SELECT * FROM upsert_time_offset_5
key       text      offset
-----------------------------
hazelnut  hazelnut  0

#
# Relative timestamps
#
# These tests are mainly meant as smoke tests. We can't do good tests currently,
# because we cannot control system time in tests.
#

$ kafka-create-topic topic=t3 partitions=1

$ kafka-ingest format=bytes topic=t3 timestamp=1
apple

# Timestamp for June 2021
$ kafka-ingest format=bytes topic=t3 timestamp=1622666300000
banana

# Timestamp for June 2099
$ kafka-ingest format=bytes topic=t3 timestamp=4084108700000
cherry

> CREATE CLUSTER relative_time_offset_30_years_ago_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE relative_time_offset_30_years_ago
  IN CLUSTER relative_time_offset_30_years_ago_cluster
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=-946100000000, TOPIC 'testdrive-t3-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET

> CREATE CLUSTER relative_time_offset_today_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE relative_time_offset_today
  IN CLUSTER relative_time_offset_today_cluster
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=-1, TOPIC 'testdrive-t3-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET

> SELECT * FROM relative_time_offset_30_years_ago
text      offset
-------------------
banana    1
cherry    2

> SELECT * FROM relative_time_offset_today
text      offset
-------------------
cherry    2

# Make sure that we don't fetch any messages that we don't want to fetch

$ kafka-create-topic topic=t4 partitions=1

$ kafka-ingest format=bytes topic=t4 timestamp=1
apple
pie

# A time offset of -1 specifies that we want to start from the end of the topic
# (negative offsets are relative from the end).
> CREATE CLUSTER verify_no_fetch_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE verify_no_fetch
  IN CLUSTER verify_no_fetch_cluster
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=-1, TOPIC 'testdrive-t4-${testdrive.seed}')
  FORMAT TEXT
  INCLUDE OFFSET


#
# UPSERT + AVRO
#

$ set keyschema={
    "type": "record",
    "name": "Key",
    "fields": [
        {"name": "id", "type": "long"}
    ]
  }

$ set schema={
    "type" : "record",
    "name" : "envelope",
    "fields" : [
      {
        "name": "before",
        "type": [
          {
            "name": "row",
            "type": "record",
            "fields": [
              {
                  "name": "id",
                  "type": "long"
              },
              {
                "name": "creature",
                "type": "string"
              }]
           },
           "null"
         ]
      },
      {
        "name": "after",
        "type": ["row", "null"]
      }
    ]
  }

$ kafka-create-topic topic=dbzupsert

$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=1
{"id": 1} {"before": {"row": {"id": 1, "creature": "fish"}}, "after": {"row": {"id": 1, "creature": "mudskipper"}}}
{"id": 1} {"before": {"row": {"id": 1, "creature": "mudskipper"}}, "after": {"row": {"id": 1, "creature": "salamander"}}}
{"id": 1} {"before": {"row": {"id": 1, "creature": "salamander"}}, "after": {"row": {"id": 1, "creature": "lizard"}}}

$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=2
{"id": 1} {"before": {"row": {"id": 1, "creature": "lizard"}}, "after": {"row": {"id": 1, "creature": "dino"}}}

$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=3
{"id": 2} {"before": null, "after": {"row": {"id": 2, "creature": "archeopteryx"}}}
{"id": 2} {"before": {"row": {"id": 2, "creature": "archeopteryx"}}, "after": {"row": {"id": 2, "creature": "velociraptor"}}}

# test duplicates
$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=4
{"id": 3} {"before": {"row": {"id": 3, "creature": "protoceratops"}}, "after": {"row": {"id": 3, "creature": "triceratops"}}}
{"id": 3} {"before": {"row": {"id": 3, "creature": "protoceratops"}}, "after": {"row": {"id": 3, "creature": "triceratops"}}}

# test removal and reinsertion
$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=5
{"id": 4} {"before": null, "after": {"row": {"id": 4, "creature": "moros"}}}

$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=6
{"id": 4} {"before": {"row": {"id": 4, "creature": "trex"}}, "after": null}

$ kafka-ingest format=avro topic=dbzupsert key-format=avro key-schema=${keyschema} schema=${schema} timestamp=7
{"id": 4} {"before": {"row": {"id": 4, "creature": "trex"}}, "after": {"row": {"id": 4, "creature": "chicken"}}}

> CREATE CLUSTER upsert_time_skip_cluster SIZE '${arg.default-storage-size}';
> CREATE SOURCE upsert_time_skip
  IN CLUSTER upsert_time_skip_cluster
  FROM KAFKA CONNECTION kafka_conn (START TIMESTAMP=6, TOPIC 'testdrive-dbzupsert-${testdrive.seed}')
  FORMAT AVRO USING CONFLUENT SCHEMA REGISTRY CONNECTION csr_conn
  ENVELOPE DEBEZIUM

> SELECT * FROM upsert_time_skip
id creature
-----------
4  chicken
