//! A basic server code example

use std::{error, sync, time};

use axum::{
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
    Json, Router,
};
use scru64::generator::NodeSpec;
use scru64_node_id_server::Engine;
use serde_json::{json, Value as JsonValue};

#[tokio::main]
async fn main() {
    let (scrambling_seed, time_to_live, bind_address) = get_params();
    let engine = match scrambling_seed {
        Some(seed) => Engine::with_scrambling_seed(seed),
        None => Engine::default(),
    };

    let app = Router::new()
        .route("/node-id-size/:size/node-id", post(request))
        .route(
            "/node-id-size/:size/node-id/:id",
            post(request_one).delete(release),
        )
        .route("/list", get(list))
        .route("/dump", get(dump))
        .with_state((sync::Arc::new(sync::Mutex::new(engine)), time_to_live));

    let listener = tokio::net::TcpListener::bind(bind_address).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

fn get_params() -> (Option<u64>, Option<time::Duration>, String) {
    // mock implementation
    (
        Some(0x42),
        Some(time::Duration::from_secs(60 * 60 * 24)),
        String::from("0.0.0.0:3000"),
    )
}

type AppState = (sync::Arc<sync::Mutex<Engine>>, Option<time::Duration>);

async fn request(
    Path(node_id_size): Path<u8>,
    State((engine, time_to_live)): State<AppState>,
) -> (StatusCode, Json<JsonValue>) {
    if !(4..=20).contains(&node_id_size) {
        return (
            StatusCode::BAD_REQUEST,
            Json(json!({ "error": "node_id_size must be between 4 and 20" })),
        );
    }

    if let Some(ttl) = time_to_live {
        match engine.lock().unwrap().request_with_ttl(node_id_size, ttl) {
            Ok((issued, expiry_time)) => (
                StatusCode::CREATED,
                Json(json!({
                    "ok": "issued",
                    "node": ser_node_spec(issued),
                    "expires_at": ser_expiry_time(expiry_time),
                })),
            ),
            Err(err) => (StatusCode::FORBIDDEN, Json(ser_error(err))),
        }
    } else {
        match engine.lock().unwrap().request(node_id_size) {
            Ok(issued) => (
                StatusCode::CREATED,
                Json(json!({ "ok": "issued", "node": ser_node_spec(issued) })),
            ),
            Err(err) => (StatusCode::FORBIDDEN, Json(ser_error(err))),
        }
    }
}

async fn request_one(
    Path((node_id_size, node_id)): Path<(u8, u32)>,
    State((engine, time_to_live)): State<AppState>,
) -> (StatusCode, Json<JsonValue>) {
    let node_spec = match NodeSpec::with_node_id(node_id, node_id_size) {
        Ok(t) => t,
        Err(err) => return (StatusCode::BAD_REQUEST, Json(ser_error(err))),
    };

    if let Some(ttl) = time_to_live {
        match engine.lock().unwrap().request_one_with_ttl(node_spec, ttl) {
            Ok(expiry_time) => (
                StatusCode::OK,
                Json(json!({
                    "ok": "reserved",
                    "node": ser_node_spec(node_spec),
                    "expires_at": ser_expiry_time(expiry_time),
                })),
            ),
            Err(err) => (StatusCode::FORBIDDEN, Json(ser_error(err))),
        }
    } else {
        match engine.lock().unwrap().request_one(node_spec) {
            Ok(_) => (
                StatusCode::OK,
                Json(json!({ "ok": "reserved", "node": ser_node_spec(node_spec) })),
            ),
            Err(err) => (StatusCode::FORBIDDEN, Json(ser_error(err))),
        }
    }
}

async fn release(
    Path((node_id_size, node_id)): Path<(u8, u32)>,
    State((engine, _)): State<AppState>,
) -> (StatusCode, Json<JsonValue>) {
    let node_spec = match NodeSpec::with_node_id(node_id, node_id_size) {
        Ok(t) => t,
        Err(err) => return (StatusCode::BAD_REQUEST, Json(ser_error(err))),
    };

    match engine.lock().unwrap().release(node_spec) {
        Ok(_) => (
            StatusCode::OK,
            Json(json!({ "ok": "released", "node": ser_node_spec(node_spec) })),
        ),
        Err(err) => (StatusCode::FORBIDDEN, Json(ser_error(err))),
    }
}

async fn list(State((engine, _)): State<AppState>) -> Json<JsonValue> {
    let mut lock = engine.lock().unwrap();
    lock.vacuum();
    Json(json!({ "node_specs": Vec::from_iter(lock.iter()) }))
}

async fn dump(State((engine, _)): State<AppState>) -> Json<JsonValue> {
    let mut lock = engine.lock().unwrap();
    lock.vacuum();
    Json(json!({ "engine": *lock }))
}

fn ser_node_spec(node_spec: NodeSpec) -> impl serde::Serialize {
    #[derive(serde::Serialize)]
    struct Node {
        id: u32,
        id_size: u8,
        spec: NodeSpec,
    }

    Node {
        id: node_spec.node_id(),
        id_size: node_spec.node_id_size(),
        spec: node_spec,
    }
}

fn ser_expiry_time(expiry_time: time::SystemTime) -> impl serde::Serialize {
    expiry_time
        .duration_since(time::UNIX_EPOCH)
        .expect("unix timestamp should be available")
        .as_secs_f64()
}

fn ser_error(err: impl error::Error) -> JsonValue {
    json!({ "error": err.to_string() })
}
