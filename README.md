# SCRU64 `node_id` Server

This crate includes functions to develop a SCRU64 `node_id` server that assigns
non-overlapping `node_id`s of various `node_id_size`s to distributed SCRU64
generators. Refer to [the examples directory] for concrete usage.

See also [SCRU64 Specification](https://github.com/scru64/spec).

[the examples directory]: https://github.com/scru64/node-id-server/tree/main/examples

## Usage examples

Launch the example basic server:

```bash
cargo run --example basic
```

Request `node_id`s of various `node_id_size`s:

```bash
curl -X POST http://0.0.0.0:3000/node-id-size/8/node-id
curl -X POST http://0.0.0.0:3000/node-id-size/4/node-id
curl -X POST http://0.0.0.0:3000/node-id-size/8/node-id
curl -X POST http://0.0.0.0:3000/node-id-size/12/node-id
curl -X POST http://0.0.0.0:3000/node-id-size/4/node-id
curl -X POST http://0.0.0.0:3000/node-id-size/8/node-id
```

Request specific `node_id`s:

```bash
curl -X POST http://0.0.0.0:3000/node-id-size/8/node-id/130
curl -X POST http://0.0.0.0:3000/node-id-size/8/node-id/131
```

Release unnecessary `node_id`s:

```bash
curl -X DELETE http://0.0.0.0:3000/node-id-size/8/node-id/68
curl -X DELETE http://0.0.0.0:3000/node-id-size/4/node-id/6
```

Print all the active `node_id`s:

```bash
curl -X GET http://0.0.0.0:3000/list
```

Dump the server state:

```bash
curl -X GET http://0.0.0.0:3000/dump
```
