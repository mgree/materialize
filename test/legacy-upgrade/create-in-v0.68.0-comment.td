# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

$ postgres-connect name=mz_system url=postgres://mz_system:materialize@${testdrive.materialize-internal-sql-addr}

$[version<=12600] postgres-execute connection=mz_system
ALTER SYSTEM SET enable_comment = true;

> CREATE TABLE comment_table ( x int8, y text );
> CREATE VIEW comment_view AS SELECT x FROM comment_table;

> COMMENT ON TABLE comment_table IS 'foo';
> COMMENT ON COLUMN comment_table.x IS 'load_bearing';
> COMMENT ON VIEW comment_view IS 'subset_of_comment_table';
