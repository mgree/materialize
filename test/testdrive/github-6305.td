# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

# Regression test for https://github.com/MaterializeInc/database-issues/issues/1947

> CREATE TABLE t1 (i1 INT8);

> BEGIN

> DECLARE c CURSOR FOR SUBSCRIBE (SELECT * FROM t1) AS OF 18446744073709551615

> FETCH 0 c

> FETCH 0 c WITH (timeout='1h')

> COMMIT
