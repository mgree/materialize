# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

$ postgres-execute connection=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}
ALTER SYSTEM SET enable_within_timestamp_order_by_in_subscribe = true;
ALTER SYSTEM SET enable_envelope_debezium_in_subscribe = true;

$ set-regex match=\d{13,20} replacement=<TIMESTAMP>

$ postgres-connect name=mz_system url=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) WITHIN TIMESTAMP ORDER BY a, mz_diff
> FETCH 1 c
<TIMESTAMP> 1 1 2

> FETCH 1 c
<TIMESTAMP> 1 2 1
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) WITHIN TIMESTAMP ORDER BY a, b
> FETCH 1 c
<TIMESTAMP> 1 1 2

> FETCH 1 c
<TIMESTAMP> 1 2 1
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) WITHIN TIMESTAMP ORDER BY b, a
> FETCH 1 c
<TIMESTAMP> 1 2 1

> FETCH 1 c
<TIMESTAMP> 1 1 2
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) WITHIN TIMESTAMP ORDER BY b DESC NULLS LAST, a ASC
> FETCH 1 c
<TIMESTAMP> 1 1 2

> FETCH 1 c
<TIMESTAMP> 1 2 1
> COMMIT

> CREATE TABLE t(a int, b int, c int)
> INSERT INTO t VALUES (1,2,3), (4,0,-4), (2,5,-6)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t)
> FETCH 3 c
<TIMESTAMP> 1 1 2 3
<TIMESTAMP> 1 4 0 -4
<TIMESTAMP> 1 2 5 -6
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t) WITHIN TIMESTAMP ORDER BY a, b, c
> FETCH 1 c
<TIMESTAMP> 1 1 2 3
> FETCH 1 c
<TIMESTAMP> 1 2 5 -6
> FETCH 1 c
<TIMESTAMP> 1 4 0 -4
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE t WITHIN TIMESTAMP ORDER BY a, b, c
> FETCH 1 c
<TIMESTAMP> 1 1 2 3
> FETCH 1 c
<TIMESTAMP> 1 2 5 -6
> FETCH 1 c
<TIMESTAMP> 1 4 0 -4
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t) WITHIN TIMESTAMP ORDER BY c, b, mz_diff, a
> FETCH 1 c
<TIMESTAMP> 1 2 5 -6
> FETCH 1 c
<TIMESTAMP> 1 4 0 -4
> FETCH 1 c
<TIMESTAMP> 1 1 2 3
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE t WITHIN TIMESTAMP ORDER BY c, b, mz_diff, a
> FETCH 1 c
<TIMESTAMP> 1 2 5 -6
> FETCH 1 c
<TIMESTAMP> 1 4 0 -4
> FETCH 1 c
<TIMESTAMP> 1 1 2 3
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE t WITHIN TIMESTAMP ORDER BY 4, 3, 1, 2  -- same as above
> FETCH 1 c
<TIMESTAMP> 1 2 5 -6
> FETCH 1 c
<TIMESTAMP> 1 4 0 -4
> FETCH 1 c
<TIMESTAMP> 1 1 2 3
> COMMIT

> CREATE TABLE t0(key int, value int)
> INSERT INTO t0 VALUES (1, 2), (2, 3)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t0) WITHIN TIMESTAMP ORDER BY key, mz_diff
> FETCH 1 c
<TIMESTAMP> 1 1 2

> FETCH 1 c
<TIMESTAMP> 1 2 3

$ postgres-execute connection=mz_system
UPDATE t0 SET value = 4 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> -1 1 2

> FETCH 1 c
<TIMESTAMP> 1 1 4
> COMMIT

# make sure progress messages are ok
> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE t WITH (PROGRESS, SNAPSHOT) WITHIN TIMESTAMP ORDER BY c, b, a
> FETCH 1 c
<TIMESTAMP> true <null> <null> <null> <null>
> FETCH 3 c
<TIMESTAMP> false 1 2 5 -6
<TIMESTAMP> false 1 4 0 -4
<TIMESTAMP> false 1 1 2 3
> COMMIT


! SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) WITHIN TIMESTAMP ORDER BY c
contains: column "c" does not exist

! SUBSCRIBE (SELECT 1 as c, 2 as c union select 2, 1) WITHIN TIMESTAMP ORDER BY c
contains: column reference "c" is ambiguous

! SUBSCRIBE (SELECT 1 as a) WITHIN TIMESTAMP ORDER BY mz_diff + 1 DESC
contains: invalid ORDER BY in SUBSCRIBE WITHIN TIMESTAMP ORDER BY

! SUBSCRIBE (SELECT 1 as a) WITHIN TIMESTAMP ORDER BY a + 1 DESC
contains: invalid ORDER BY in SUBSCRIBE WITHIN TIMESTAMP ORDER BY

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) ENVELOPE UPSERT (KEY (a, b))
> FETCH 1 c
<TIMESTAMP> upsert 1 2

> FETCH 1 c
<TIMESTAMP> upsert 2 1
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) ENVELOPE UPSERT (KEY (b, a))
> FETCH 1 c
<TIMESTAMP> upsert 1 2

> FETCH 1 c
<TIMESTAMP> upsert 2 1
> COMMIT

> CREATE TABLE t1(key int, value int, UNIQUE (key))
> INSERT INTO t1 VALUES (1, 2), (2, 3)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t1) ENVELOPE UPSERT (KEY (key))
> FETCH 2 c
<TIMESTAMP> upsert 1 2
<TIMESTAMP> upsert 2 3

$ postgres-execute connection=mz_system
UPDATE t1 SET value = 4 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> upsert 1 4

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> delete 1 <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 1), (1, 1)

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null>

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 1), (1, 2)

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 3)

> FETCH 1 c
<TIMESTAMP> upsert 1 3

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1 AND value = 1

> FETCH 1 c
<TIMESTAMP> delete 1 <null>

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null>

> COMMIT

> CREATE TABLE t2(value int, key int, UNIQUE (key))
> INSERT INTO t2 VALUES (2, 1), (3, 2)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t2) ENVELOPE UPSERT (KEY (key))
> FETCH 2 c
<TIMESTAMP> upsert 1 2
<TIMESTAMP> upsert 2 3

$ postgres-execute connection=mz_system
UPDATE t2 SET value = 4 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> upsert 1 4

$ postgres-execute connection=mz_system
DELETE FROM t2 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> delete 1 <null>

> COMMIT

# make sure progress messages are ok
> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t2) WITH (PROGRESS, SNAPSHOT) ENVELOPE UPSERT (KEY (key))
> FETCH 1 c
<TIMESTAMP> true <null> <null> <null>

> FETCH 1 c
<TIMESTAMP> false upsert 2 3

> FETCH 1 c
<TIMESTAMP> true <null> <null> <null>

> COMMIT

! SUBSCRIBE (SELECT * FROM t2) WITH (PROGRESS, SNAPSHOT) ENVELOPE UPSERT (KEY (invalid_key))
contains: column "invalid_key" does not exist


> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) ENVELOPE DEBEZIUM (KEY (a, b))
> FETCH 1 c
<TIMESTAMP> insert 1 2

> FETCH 1 c
<TIMESTAMP> insert 2 1
> COMMIT

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT 1 as a, 2 as b union select 2, 1) ENVELOPE DEBEZIUM (KEY (b, a))
> FETCH 1 c
<TIMESTAMP> insert 1 2

> FETCH 1 c
<TIMESTAMP> insert 2 1
> COMMIT

> DROP TABLE t1 CASCADE
> CREATE TABLE t1(key int, value int, UNIQUE (key))
> INSERT INTO t1 VALUES (1, 2), (2, 3)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t1) ENVELOPE DEBEZIUM (KEY (key))
> FETCH 2 c
<TIMESTAMP> insert 1 <null> 2
<TIMESTAMP> insert 2 <null> 3

$ postgres-execute connection=mz_system
UPDATE t1 SET value = 4 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> upsert 1 2 4

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> delete 1 4 <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 1), (1, 1)

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null> <null>

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null> <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 1), (1, 2)

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null> <null>

$ postgres-execute connection=mz_system
INSERT INTO t1 VALUES (1, 3)

> FETCH 1 c
<TIMESTAMP> insert 1 <null> 3

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1 AND value = 1

> FETCH 1 c
<TIMESTAMP> delete 1 1 <null>

$ postgres-execute connection=mz_system
DELETE FROM t1 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> "key_violation" 1 <null> <null>

> COMMIT

> DROP TABLE t2 CASCADE
> CREATE TABLE t2(value int, key int, UNIQUE (key))
> INSERT INTO t2 VALUES (2, 1), (3, 2)

> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t2) ENVELOPE DEBEZIUM (KEY (key))
> FETCH 2 c
<TIMESTAMP> insert 1 <null> 2
<TIMESTAMP> insert 2 <null> 3

$ postgres-execute connection=mz_system
UPDATE t2 SET value = 4 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> upsert 1 2 4

$ postgres-execute connection=mz_system
DELETE FROM t2 WHERE key = 1

> FETCH 1 c
<TIMESTAMP> delete 1 4 <null>

> COMMIT

# make sure progress messages are ok
> BEGIN
> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t2) WITH (PROGRESS, SNAPSHOT) ENVELOPE DEBEZIUM (KEY (key))
> FETCH 1 c
<TIMESTAMP> true <null> <null> <null> <null>

> FETCH 1 c
<TIMESTAMP> false insert 2 <null> 3

> FETCH 1 c
<TIMESTAMP> true <null> <null> <null> <null>

> COMMIT

! SUBSCRIBE (SELECT * FROM t2) WITH (PROGRESS, SNAPSHOT) ENVELOPE DEBEZIUM (KEY (invalid_key))
contains: column "invalid_key" does not exist

# SUBSCRIBE with a query that has a `RowSetFinishing`, which needs to be turned into a TopK

> CREATE TABLE t3 (a int, b int);

> INSERT INTO t3 VALUES (1,2), (3,4), (5,6), (7,8);

> CREATE VIEW limited AS
  SELECT * FROM t3
  ORDER BY a DESC, b
  LIMIT 3;

> BEGIN;

> DECLARE c CURSOR FOR SUBSCRIBE limited;

> FETCH 2 c;
<TIMESTAMP> 1 5 6
<TIMESTAMP> 1 3 4

> COMMIT;

# Subscribe with a query that uses two columns for upsert key.

> CREATE TABLE t4 (a int, b text, c uuid);

> INSERT INTO t4 VALUES (1, 'foo', '30a7947e-4b38-46a4-b7c2-602ba62ce20b');

> BEGIN;
> DECLARE c4u CURSOR FOR SUBSCRIBE t4 ENVELOPE UPSERT (KEY (c, a));

> FETCH 1 c4u;
<TIMESTAMP> upsert 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 foo

$ postgres-execute connection=mz_system
UPDATE t4 SET b = 'bar' WHERE a = 1

> FETCH 1 c4u;
<TIMESTAMP> upsert 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 bar

$ postgres-execute connection=mz_system
DELETE FROM t4 WHERE b = 'bar'

> FETCH 1 c4u;
<TIMESTAMP> delete 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 <null>

> COMMIT;

> INSERT INTO t4 VALUES (1, 'foo', '30a7947e-4b38-46a4-b7c2-602ba62ce20b');

> BEGIN;
> DECLARE c4d CURSOR FOR SUBSCRIBE t4 ENVELOPE DEBEZIUM (KEY (c, a));

> FETCH 1 c4d;
<TIMESTAMP> insert 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 <null> foo

$ postgres-execute connection=mz_system
UPDATE t4 SET b = 'bar' WHERE a = 1

> FETCH 1 c4d;
<TIMESTAMP> upsert 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 foo bar

$ postgres-execute connection=mz_system
DELETE FROM t4 WHERE b = 'bar'

> FETCH 1 c4d;
<TIMESTAMP> delete 30a7947e-4b38-46a4-b7c2-602ba62ce20b 1 bar <null>

> COMMIT;
