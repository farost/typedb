/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use cucumber::gherkin::Step;
use database::{
    transaction::{DataCommitError, SchemaCommitError, TransactionRead, TransactionSchema, TransactionWrite},
    Database,
};
use futures::future::join_all;
use itertools::Either;
use macro_rules_attribute::apply;
use options::TransactionOptions;
use params::{self, check_boolean};
use server::server::Server;
use storage::durability_client::WALClient;
use test_utils::assert_matches;

use crate::{connection::BehaviourConnectionTestExecutionError, generic_step, util, ActiveTransaction, Context};

async fn server_open_transaction_for_database(
    server: &'_ Server,
    tx_name: String,
    database_name: &'_ str,
) -> ActiveTransaction {
    let database = server.database_manager().database(database_name).expect("Expected database");
    match tx_name.as_str() {
        "read" => ActiveTransaction::Read(
            TransactionRead::open(database, TransactionOptions::default()).expect("Read transaction"),
        ),
        "write" => ActiveTransaction::Write(
            TransactionWrite::open(database, TransactionOptions::default()).expect("Write transaction"),
        ),
        "schema" => ActiveTransaction::Schema(
            TransactionSchema::open(database, TransactionOptions::default()).expect("Schema transaction"),
        ),
        _ => unreachable!("Unrecognised transaction type"),
    }
}

fn transaction_type_matches(tx: &ActiveTransaction, tx_type: &str) {
    match tx_type {
        "read" => assert_matches!(tx, ActiveTransaction::Read(_)),
        "write" => assert_matches!(tx, ActiveTransaction::Write(_)),
        "schema" => assert_matches!(tx, ActiveTransaction::Schema(_)),
        _ => unreachable!("Unrecognised transaction type"),
    };
}

#[apply(generic_step)]
#[step(expr = "connection open {word} transaction for database: {word}")]
pub async fn connection_open_transaction(context: &mut Context, tx_type: String, database_name: String) {
    assert!(context.transaction().is_none(), "Existing transaction must be closed first");
    let server = context.server().expect("Expected server").lock().unwrap();
    let tx = server_open_transaction_for_database(&server, tx_type, &database_name).await;
    drop(server);
    context.set_transaction(tx);
}

#[apply(generic_step)]
#[step(expr = "connection open transaction(s) for database: {word}, of type:")]
pub async fn connection_open_transactions(context: &mut Context, database_name: String, step: &Step) {
    let server = context.server().expect("Expected server").lock().unwrap();
    let mut transactions = vec![];
    for tx_type in util::iter_table(step) {
        transactions.push(server_open_transaction_for_database(&server, tx_type.into(), &database_name).await);
    }
    drop(server);
    context.set_concurrent_transactions(transactions);
}

#[apply(generic_step)]
#[step(expr = "connection open transaction(s) in parallel for database: {word}, of type:")]
pub async fn connection_open_transactions_in_parallel(context: &mut Context, database_name: String, step: &Step) {
    let server = context.server().expect("Expected server").lock().unwrap();
    let transactions: Vec<ActiveTransaction> = join_all(
        util::iter_table(step)
            .map(|tx_type| server_open_transaction_for_database(&server, tx_type.into(), &database_name)),
    )
    .await;
    drop(server);
    context.set_concurrent_transactions(transactions);
}

#[apply(generic_step)]
#[step(expr = "transaction is open: {boolean}")]
pub async fn transaction_is_open(context: &mut Context, is_open: params::Boolean) {
    check_boolean!(is_open, context.transaction().is_some());
}

#[apply(generic_step)]
#[step(expr = "transactions( in parallel) are open: {boolean}")]
pub async fn transactions_in_parallel_are_open(context: &mut Context, are_open: params::Boolean) {
    check_boolean!(are_open, !context.get_concurrent_transactions().is_empty());
}

#[apply(generic_step)]
#[step(expr = "transaction has type: {word}")]
pub async fn transaction_has_type(context: &mut Context, tx_type: String) {
    transaction_type_matches(context.transaction().unwrap(), &tx_type)
}

#[apply(generic_step)]
#[step(expr = "transactions( in parallel) have type:")]
pub async fn transactions_in_parallel_have_type(context: &mut Context, step: &Step) {
    let mut active_transaction_iter = context.get_concurrent_transactions().iter();
    for tx_type in util::iter_table(step) {
        transaction_type_matches(active_transaction_iter.next().unwrap(), tx_type)
    }
    assert!(active_transaction_iter.next().is_none(), "Opened more transactions than tested!")
}

#[apply(generic_step)]
#[step(expr = "transaction commits{may_error}")]
pub async fn transaction_commits(context: &mut Context, may_error: params::MayError) {
    match context.take_transaction().unwrap() {
        ActiveTransaction::Read(_) => {
            may_error.check::<(), BehaviourConnectionTestExecutionError>(Err(
                BehaviourConnectionTestExecutionError::CannotCommitReadTransaction,
            ));
        }
        ActiveTransaction::Write(tx) => {
            if let Either::Right(error) = may_error.check(tx.commit()) {
                match error {
                    DataCommitError::ConceptWriteErrors { write_errors: errors, .. } => {
                        for error in errors {
                            may_error.check_concept_write_without_read_errors::<()>(&Err(Box::new(error)));
                        }
                    }
                    DataCommitError::ConceptWriteErrorsFirst { typedb_source } => {
                        may_error.check_concept_write_without_read_errors::<()>(&Err(typedb_source));
                    }
                    DataCommitError::SnapshotInUse { .. } | DataCommitError::SnapshotError { .. } => {
                        panic!("Unexpected write commit error: {:?}", error);
                    }
                }
            }
        }
        ActiveTransaction::Schema(tx) => {
            let types_syntax =  tx.type_manager.get_types_syntax(tx.snapshot.as_ref()).unwrap();
            let schema = format!("define\n{}", types_syntax);
            if let Either::Right(error) = may_error.check(tx.commit()) {
                match error {
                    SchemaCommitError::ConceptWriteErrors { write_errors: errors, .. } => {
                        for error in errors {
                            may_error.check_concept_write_without_read_errors::<()>(&Err(Box::new(error)));
                        }
                    }
                    SchemaCommitError::ConceptWriteErrorsFirst { typedb_source } => {
                        may_error.check_concept_write_without_read_errors::<()>(&Err(typedb_source));
                    }
                    SchemaCommitError::FunctionError { .. } => {}
                    SchemaCommitError::TypeCacheUpdateError { .. }
                    | SchemaCommitError::StatisticsError { .. }
                    | SchemaCommitError::SnapshotError { .. } => {
                        panic!("Unexpected schema commit error: {:?}", error);
                    }
                }
            }

            // after each schema trasaction, we re-test the schema export/import
            test_schema_export(context, &schema);
        }
    }
}

fn test_schema_export(context: &mut Context, schema: &str) {
    // export, re-import, and export schema and verify that's equal!
    let guard = context.server.as_ref().unwrap().lock().unwrap();
    let database_manager = guard.database_manager();
    if !schema.trim().is_empty() {
        const REIMPORT_DB: &str = "schema_reimport_from_test_tmp";
        database_manager.create_database(REIMPORT_DB).unwrap();
        let reimport = database_manager.database(REIMPORT_DB).unwrap();
        let mut transaction = TransactionSchema::open(reimport.clone(), TransactionOptions::default()).unwrap();
        transaction
            .query_manager
            .execute_schema(
                Arc::get_mut(&mut transaction.snapshot).unwrap(),
                &transaction.type_manager,
                &transaction.thing_manager,
                &transaction.function_manager,
                typeql::parse_query(&schema).unwrap().into_schema(),
                schema,
            )
            .unwrap();
        transaction.commit().unwrap();

        let re_exported_schema = get_schema(reimport.clone());
        assert_eq!(re_exported_schema, schema);
        drop(reimport);
        let result = database_manager.delete_database(REIMPORT_DB);

        result.unwrap();
    }
}

fn get_schema(database: Arc<Database<WALClient>>) -> String {
    let transaction = TransactionRead::open(database, TransactionOptions::default()).unwrap();
    let types_syntax = transaction.type_manager.get_types_syntax(transaction.snapshot()).unwrap();
    let mut schema = format!("define\n{}", types_syntax);
    schema
}

#[apply(generic_step)]
#[step(expr = "transaction rollbacks{may_error}")]
pub async fn transaction_rollbacks(context: &mut Context, may_error: params::MayError) {
    match context.take_transaction().unwrap() {
        ActiveTransaction::Read(_) => {
            may_error.check::<(), BehaviourConnectionTestExecutionError>(Err(
                BehaviourConnectionTestExecutionError::CannotRollbackReadTransaction,
            ));
        }
        ActiveTransaction::Write(mut tx) => {
            tx.rollback();
            context.set_transaction(ActiveTransaction::Write(tx))
        }
        ActiveTransaction::Schema(mut tx) => {
            tx.rollback();
            context.set_transaction(ActiveTransaction::Schema(tx))
        }
    }
}

#[apply(generic_step)]
#[step(expr = "transaction closes")]
pub async fn transaction_closes(context: &mut Context) {
    context.close_active_transaction()
}
