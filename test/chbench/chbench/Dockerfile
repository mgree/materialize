# Copyright Materialize, Inc. and contributors. All rights reserved.
#
# Use of this software is governed by the Business Source License
# included in the LICENSE file at the root of this repository.
#
# As of the Change Date specified in that file, in accordance with
# the Business Source License, use of this software will be governed
# by the Apache License, Version 2.0.

MZFROM ubuntu-base AS build

RUN apt-get update \
    && TZ=UTC DEBIAN_FRONTEND=noninteractive apt-get install -y \
        build-essential \
        cmake \
        curl \
        gnupg2 \
        libconfig++-dev \
        libmysqlclient-dev \
        libpqxx-dev \
        unixodbc-dev \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Build the MySQL ODBC connector.

COPY mysql.asc .

RUN gpg --import mysql.asc \
    && echo "trusted-key B7B3B788A8D3785C" >> ~/.gnupg/gpg.conf \
    && curl -fsSL https://dev.mysql.com/get/Downloads/Connector-ODBC/9.3/mysql-connector-odbc-9.3.0-src.tar.gz > mysql-odbc.tar.gz \
    && curl -fsSL "https://dev.mysql.com/downloads/gpg/?file=mysql-connector-odbc-9.3.0-src.tar.gz&p=10" > mysql-odbc.asc \
    && gpg --verify mysql-odbc.asc mysql-odbc.tar.gz \
    && tar -xzf mysql-odbc.tar.gz

RUN cd mysql-connector-odbc-9.3.0-src \
    && cmake -DWITH_UNIXODBC=1 -DDISABLE_GUI=1 . \
    && make -j8 \
    && make install

# Build chBenchmark.

COPY . src/

RUN mkdir build && cd build \
    && cmake -DCMAKE_BUILD_TYPE=Release ../src \
    && make -j8

RUN ls build

# Copy the build artifacts into a fresh image.

MZFROM ubuntu-base

RUN apt-get update && TZ=UTC DEBIAN_FRONTEND=noninteractive apt-get install -y libconfig++9v5 libmysqlclient21 libpqxx-7.9 unixodbc && apt-get clean && rm -rf /var/lib/apt/lists/*

COPY odbc.ini /etc/odbc.ini
COPY mz-default-postgres.cfg /etc/chbenchmark/mz-default-postgres.cfg
COPY mz-default-mysql.cfg /etc/chbenchmark/mz-default-mysql.cfg
COPY --from=build /usr/local/lib/libmyodbc9a.so /usr/local/lib/libmyodbc9a.so
COPY --from=build /build/chbenchmark /usr/local/bin/chBenchmark

ENTRYPOINT ["chBenchmark"]
