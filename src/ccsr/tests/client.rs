// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

// BEGIN LINT CONFIG
// DO NOT EDIT. Automatically generated by bin/gen-lints.
// Have complaints about the noise? See the note in misc/python/materialize/cli/gen-lints.py first.
#![allow(clippy::style)]
#![allow(clippy::complexity)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::mutable_key_type)]
#![allow(clippy::stable_sort_primitive)]
#![allow(clippy::map_entry)]
#![allow(clippy::box_default)]
#![warn(clippy::bool_comparison)]
#![warn(clippy::clone_on_ref_ptr)]
#![warn(clippy::no_effect)]
#![warn(clippy::unnecessary_unwrap)]
#![warn(clippy::dbg_macro)]
#![warn(clippy::todo)]
#![warn(clippy::wildcard_dependencies)]
#![warn(clippy::zero_prefixed_literal)]
#![warn(clippy::borrowed_box)]
#![warn(clippy::deref_addrof)]
#![warn(clippy::double_must_use)]
#![warn(clippy::double_parens)]
#![warn(clippy::extra_unused_lifetimes)]
#![warn(clippy::needless_borrow)]
#![warn(clippy::needless_question_mark)]
#![warn(clippy::needless_return)]
#![warn(clippy::redundant_pattern)]
#![warn(clippy::redundant_slicing)]
#![warn(clippy::redundant_static_lifetimes)]
#![warn(clippy::single_component_path_imports)]
#![warn(clippy::unnecessary_cast)]
#![warn(clippy::useless_asref)]
#![warn(clippy::useless_conversion)]
#![warn(clippy::builtin_type_shadow)]
#![warn(clippy::duplicate_underscore_argument)]
#![warn(clippy::double_neg)]
#![warn(clippy::unnecessary_mut_passed)]
#![warn(clippy::wildcard_in_or_patterns)]
#![warn(clippy::crosspointer_transmute)]
#![warn(clippy::excessive_precision)]
#![warn(clippy::overflow_check_conditional)]
#![warn(clippy::as_conversions)]
#![warn(clippy::match_overlapping_arm)]
#![warn(clippy::zero_divided_by_zero)]
#![warn(clippy::must_use_unit)]
#![warn(clippy::suspicious_assignment_formatting)]
#![warn(clippy::suspicious_else_formatting)]
#![warn(clippy::suspicious_unary_op_formatting)]
#![warn(clippy::mut_mutex_lock)]
#![warn(clippy::print_literal)]
#![warn(clippy::same_item_push)]
#![warn(clippy::useless_format)]
#![warn(clippy::write_literal)]
#![warn(clippy::redundant_closure)]
#![warn(clippy::redundant_closure_call)]
#![warn(clippy::unnecessary_lazy_evaluations)]
#![warn(clippy::partialeq_ne_impl)]
#![warn(clippy::redundant_field_names)]
#![warn(clippy::transmutes_expressible_as_ptr_casts)]
#![warn(clippy::unused_async)]
#![warn(clippy::disallowed_methods)]
#![warn(clippy::disallowed_macros)]
#![warn(clippy::disallowed_types)]
#![warn(clippy::from_over_into)]
// END LINT CONFIG

use std::env;

use hyper::server::conn::AddrIncoming;
use hyper::{service, Body, Response, Server, StatusCode};
use mz_ccsr::{
    Client, DeleteError, GetByIdError, GetBySubjectError, PublishError, SchemaReference, SchemaType,
};
use once_cell::sync::Lazy;

pub static SCHEMA_REGISTRY_URL: Lazy<reqwest::Url> =
    Lazy::new(|| match env::var("SCHEMA_REGISTRY_URL") {
        Ok(addr) => addr.parse().expect("unable to parse SCHEMA_REGISTRY_URL"),
        _ => "http://localhost:8081".parse().unwrap(),
    });

#[mz_ore::test(tokio::test)]
#[cfg_attr(coverage, ignore)] // https://github.com/MaterializeInc/materialize/issues/18900
#[cfg_attr(miri, ignore)] // unsupported operation: can't call foreign function `TLS_method` on OS `linux`
async fn test_client() -> Result<(), anyhow::Error> {
    let client = mz_ccsr::ClientConfig::new(SCHEMA_REGISTRY_URL.clone()).build()?;

    let existing_subjects = client.list_subjects().await?;
    for s in existing_subjects {
        if s.starts_with("ccsr-test-") {
            client.delete_subject(&s).await?;
        }
    }

    let schema_v1 = r#"{ "type": "record", "name": "na", "fields": [
        { "name": "a", "type": "long" }
    ]}"#;

    let schema_v2 = r#"{ "type": "record", "name": "na", "fields": [
        { "name": "a", "type": "long" },
        { "name": "b", "type": "long", "default": 0 }
    ]}"#;

    let schema_v2_incompat = r#"{ "type": "record", "name": "na", "fields": [
        { "name": "a", "type": "string" }
    ]}"#;

    assert_eq!(count_schemas(&client, "ccsr-test-").await?, 0);

    let schema_v1_id = client
        .publish_schema("ccsr-test-schema", schema_v1, SchemaType::Avro, &[])
        .await?;
    assert!(schema_v1_id > 0);

    match client
        .publish_schema(
            "ccsr-test-schema",
            schema_v2_incompat,
            SchemaType::Avro,
            &[],
        )
        .await
    {
        Err(PublishError::IncompatibleSchema) => (),
        res => panic!("expected IncompatibleSchema error, got {:?}", res),
    }

    {
        let res = client.get_schema_by_subject("ccsr-test-schema").await?;
        assert_eq!(schema_v1_id, res.id);
        assert_raw_schemas_eq(schema_v1, &res.raw);
    }

    let schema_v2_id = client
        .publish_schema("ccsr-test-schema", schema_v2, SchemaType::Avro, &[])
        .await?;
    assert!(schema_v2_id > 0);
    assert!(schema_v2_id > schema_v1_id);

    assert_eq!(
        schema_v1_id,
        client
            .publish_schema("ccsr-test-schema", schema_v1, SchemaType::Avro, &[])
            .await?
    );

    {
        let res1 = client.get_schema_by_id(schema_v1_id).await?;
        let res2 = client.get_schema_by_id(schema_v2_id).await?;
        assert_eq!(schema_v1_id, res1.id);
        assert_eq!(schema_v2_id, res2.id);
        assert_raw_schemas_eq(schema_v1, &res1.raw);
        assert_raw_schemas_eq(schema_v2, &res2.raw);
    }

    {
        let res = client.get_schema_by_subject("ccsr-test-schema").await?;
        assert_eq!(schema_v2_id, res.id);
        assert_raw_schemas_eq(schema_v2, &res.raw);
    }

    assert_eq!(count_schemas(&client, "ccsr-test-").await?, 1);

    client
        .publish_schema("ccsr-test-another-schema", "\"int\"", SchemaType::Avro, &[])
        .await?;
    assert_eq!(count_schemas(&client, "ccsr-test-").await?, 2);

    {
        let subject_with_slashes = "ccsr/test/schema";
        let schema_test_id = client
            .publish_schema(subject_with_slashes, schema_v1, SchemaType::Avro, &[])
            .await?;
        assert!(schema_test_id > 0);

        let res = client.get_schema_by_subject(subject_with_slashes).await?;
        assert_eq!(schema_test_id, res.id);
        assert_raw_schemas_eq(schema_v1, &res.raw);

        let res = client.get_subject(subject_with_slashes).await?;
        assert_eq!(1, res.version);
        assert_eq!(subject_with_slashes, res.name);
        assert_eq!(schema_test_id, res.schema.id);
        assert_raw_schemas_eq(schema_v1, &res.schema.raw);
    }

    Ok(())
}

#[mz_ore::test(tokio::test)]
#[cfg_attr(miri, ignore)] // unsupported operation: can't call foreign function `TLS_method` on OS `linux`
async fn test_client_subject_and_references() -> Result<(), anyhow::Error> {
    let client = mz_ccsr::ClientConfig::new(SCHEMA_REGISTRY_URL.clone()).build()?;

    let existing_subjects = client.list_subjects().await?;
    for s in existing_subjects {
        if s.starts_with("ccsr-test-") {
            client.delete_subject(&s).await?;
        }
    }
    assert_eq!(count_schemas(&client, "ccsr-test-").await?, 0);

    let schema0_subject = "schema0.proto".to_owned();
    let schema0 = r#"
        syntax = "proto3";

        message Choice {
            string field0 = 1;
            int64 field2 = 2;
        }
    "#;

    let schema1_subject = "schema1.proto".to_owned();
    let schema1 = r#"
        syntax = "proto3";
        import "schema0.proto";

        message ChoiceId {
            string id = 1;
            Choice choice = 2;
        }
    "#;

    let schema2_subject = "schema2.proto".to_owned();
    let schema2 = r#"
        syntax = "proto3";

        import "schema0.proto";
        import "schema1.proto";

        message OtherThingWhoKnowWhatEven {
            string whatever = 1;
            ChoiceId nonsense = 2;
            Choice third_field = 3;
        }
    "#;

    let schema0_id = client
        .publish_schema(&schema0_subject, schema0, SchemaType::Protobuf, &[])
        .await?;
    assert!(schema0_id > 0);

    let schema1_id = client
        .publish_schema(
            &schema1_subject,
            schema1,
            SchemaType::Protobuf,
            &[SchemaReference {
                name: schema0_subject.clone(),
                subject: schema0_subject.clone(),
                version: 1,
            }],
        )
        .await?;
    assert!(schema1_id > 0);

    let schema2_id = client
        .publish_schema(
            &schema2_subject,
            schema2,
            SchemaType::Protobuf,
            &[
                SchemaReference {
                    name: schema1_subject.clone(),
                    subject: schema1_subject.clone(),
                    version: 1,
                },
                SchemaReference {
                    name: schema0_subject.clone(),
                    subject: schema0_subject.clone(),
                    version: 1,
                },
            ],
        )
        .await?;
    assert!(schema2_id > 0);

    let (primary_subject, dependency_subjects) =
        client.get_subject_and_references(&schema2_subject).await?;
    assert_eq!(schema2_subject, primary_subject.name);
    assert_eq!(2, dependency_subjects.len());
    assert_eq!(schema0_subject, dependency_subjects[0].name);
    assert_eq!(schema1_subject, dependency_subjects[1].name);

    // Also do the by-id lookup
    let (primary_subject, dependency_subjects) =
        client.get_subject_and_references_by_id(schema2_id).await?;
    assert_eq!(schema2_subject, primary_subject.name);
    assert_eq!(2, dependency_subjects.len());
    assert_eq!(schema0_subject, dependency_subjects[0].name);
    assert_eq!(schema1_subject, dependency_subjects[1].name);

    Ok(())
}

#[mz_ore::test(tokio::test)]
#[cfg_attr(miri, ignore)] // unsupported operation: can't call foreign function `TLS_method` on OS `linux`
async fn test_client_errors() -> Result<(), anyhow::Error> {
    let invalid_schema_registry_url: reqwest::Url = "data::text/plain,Info".parse().unwrap();
    match mz_ccsr::ClientConfig::new(invalid_schema_registry_url).build() {
        Err(e) => assert_eq!(
            "cannot construct a CCSR client with a cannot-be-a-base URL",
            e.to_string(),
        ),
        res => panic!("Expected error, got {:?}", res),
    }

    let client = mz_ccsr::ClientConfig::new(SCHEMA_REGISTRY_URL.clone()).build()?;

    // Get-by-id-specific errors.
    match client.get_schema_by_id(i32::max_value()).await {
        Err(GetByIdError::SchemaNotFound) => (),
        res => panic!("expected GetError::SchemaNotFound, got {:?}", res),
    }

    // Get-by-subject-specific errors.
    match client.get_schema_by_subject("ccsr-test-noexist").await {
        Err(GetBySubjectError::SubjectNotFound) => (),
        res => panic!("expected GetBySubjectError::SubjectNotFound, got {:?}", res),
    }

    // Publish-specific errors.
    match client
        .publish_schema("ccsr-test-schema", "blah", SchemaType::Avro, &[])
        .await
    {
        Err(PublishError::InvalidSchema { .. }) => (),
        res => panic!("expected PublishError::InvalidSchema, got {:?}", res),
    }

    // Delete-specific errors.
    match client.delete_subject("ccsr-test-noexist").await {
        Err(DeleteError::SubjectNotFound) => (),
        res => panic!("expected DeleteError::SubjectNotFound, got {:?}", res),
    }

    Ok(())
}

#[mz_ore::test(tokio::test)]
#[cfg_attr(miri, ignore)] // unsupported operation: can't call foreign function `TLS_method` on OS `linux`
async fn test_server_errors() -> Result<(), anyhow::Error> {
    // When the schema registry gracefully reports an error by including a
    // properly-formatted JSON document in the response, the specific error code
    // and message should be propagated.

    let client_graceful = start_server(
        StatusCode::INTERNAL_SERVER_ERROR,
        r#"{ "error_code": 50001, "message": "overloaded; try again later" }"#,
    )?;

    match client_graceful
        .publish_schema("foo", "bar", SchemaType::Avro, &[])
        .await
    {
        Err(PublishError::Server {
            code: 50001,
            ref message,
        }) if message == "overloaded; try again later" => (),
        res => panic!("expected PublishError::Server, got {:?}", res),
    }

    match client_graceful.get_schema_by_id(0).await {
        Err(GetByIdError::Server {
            code: 50001,
            ref message,
        }) if message == "overloaded; try again later" => (),
        res => panic!("expected GetByIdError::Server, got {:?}", res),
    }

    match client_graceful.get_schema_by_subject("foo").await {
        Err(GetBySubjectError::Server {
            code: 50001,
            ref message,
        }) if message == "overloaded; try again later" => (),
        res => panic!("expected GetBySubjectError::Server, got {:?}", res),
    }

    match client_graceful.delete_subject("foo").await {
        Err(DeleteError::Server {
            code: 50001,
            ref message,
        }) if message == "overloaded; try again later" => (),
        res => panic!("expected DeleteError::Server, got {:?}", res),
    }

    // If the schema registry crashes so hard that it spits out an exception
    // handler in the response, we should report the HTTP status code and a
    // generic message indicating that no further details were available.
    let client_crash = start_server(
        StatusCode::INTERNAL_SERVER_ERROR,
        r#"panic! an exception occured!"#,
    )?;

    match client_crash
        .publish_schema("foo", "bar", SchemaType::Avro, &[])
        .await
    {
        Err(PublishError::Server {
            code: 500,
            ref message,
        }) if message == "unable to decode error details" => (),
        res => panic!("expected PublishError::Server, got {:?}", res),
    }

    match client_crash.get_schema_by_id(0).await {
        Err(GetByIdError::Server {
            code: 500,
            ref message,
        }) if message == "unable to decode error details" => (),
        res => panic!("expected GetError::Server, got {:?}", res),
    }

    match client_crash.get_schema_by_subject("foo").await {
        Err(GetBySubjectError::Server {
            code: 500,
            ref message,
        }) if message == "unable to decode error details" => (),
        res => panic!("expected GetError::Server, got {:?}", res),
    }

    match client_crash.delete_subject("foo").await {
        Err(DeleteError::Server {
            code: 500,
            ref message,
        }) if message == "unable to decode error details" => (),
        res => panic!("expected DeleteError::Server, got {:?}", res),
    }

    Ok(())
}

fn start_server(status_code: StatusCode, body: &'static str) -> Result<Client, anyhow::Error> {
    let addr = {
        let incoming = AddrIncoming::bind(&([127, 0, 0, 1], 0).into()).unwrap();
        let addr = incoming.local_addr();
        let server =
            Server::builder(incoming).serve(service::make_service_fn(move |_conn| async move {
                Ok::<_, hyper::Error>(service::service_fn(move |_req| async move {
                    Response::builder()
                        .status(status_code)
                        .body(Body::from(body))
                }))
            }));
        mz_ore::task::spawn(|| "start_server", async {
            match server.await {
                Ok(()) => (),
                Err(err) => eprintln!("server error: {}", err),
            }
        });
        addr
    };

    let url: reqwest::Url = format!("http://{}", addr).parse().unwrap();
    mz_ccsr::ClientConfig::new(url).build()
}

fn assert_raw_schemas_eq(schema1: &str, schema2: &str) {
    let schema1: serde_json::Value = serde_json::from_str(schema1).unwrap();
    let schema2: serde_json::Value = serde_json::from_str(schema2).unwrap();
    assert_eq!(schema1, schema2);
}

async fn count_schemas(client: &Client, subject_prefix: &str) -> Result<usize, anyhow::Error> {
    Ok(client
        .list_subjects()
        .await?
        .iter()
        .filter(|s| s.starts_with(subject_prefix))
        .count())
}
