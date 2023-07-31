// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2023.

//! Interface for Key-Value (KV) Stores
//!
//! The KV store implementation in Tock has two levels:
//!
//! 1. **KV Level**: This level provides a standard key-value interface with
//!    common get/set/add/update/delete operations.
//!
//! 2. **KV Permissions Level**: This level mirrors the `KV` interface, but each
//!    call requires storage permissions. This permits implementing access
//!    control permissions with key-value stores in Tock.
//!
//! The expected setup inside Tock will look like this:
//!
//! ```text
//! +-----------------------+
//! |  Capsule using K-V    |
//! +-----------------------+
//!
//!    hil::kv::KVPermissions (this file)
//!
//! +-----------------------+
//! |  K-V in Tock          |
//! +-----------------------+
//!
//!    hil::kv::KV (this file)
//!
//! +-----------------------+
//! |  K-V library          |
//! +-----------------------+
//!
//!    hil::flash
//! ```

use crate::storage_permissions::StoragePermissions;
use crate::utilities::leasable_buffer::SubSliceMut;
use crate::ErrorCode;

/// Callback trait for KV stores.
///
/// Implement this trait and use `set_client()` to receive callbacks.
pub trait KVClient {
    /// This callback is called when the get operation completes.
    ///
    /// If there wasn't enough room to store the entire buffer `SIZE` will be
    /// returned in `result` and the bytes that did fit will be copied into the
    /// buffer.
    ///
    /// ### Return Values
    ///
    /// - `result`: `Ok(())` on success, `ErrorCode` on error.
    /// - `key`: The key buffer.
    /// - `value`: The value buffer.
    fn get_complete(
        &self,
        result: Result<(), ErrorCode>,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    );

    /// This callback is called when the set operation completes.
    ///
    /// ### Return Values
    ///
    /// - `result`: `Ok(())` on success, `ErrorCode` on error.
    /// - `key`: The key buffer.
    /// - `value`: The value buffer.
    fn set_complete(
        &self,
        result: Result<(), ErrorCode>,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    );

    /// This callback is called when the add operation completes.
    ///
    /// ### Return Values
    ///
    /// - `result`: `Ok(())` on success, `ErrorCode` on error.
    /// - `key`: The key buffer.
    /// - `value`: The value buffer.
    fn add_complete(
        &self,
        result: Result<(), ErrorCode>,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    );

    /// This callback is called when the update operation completes.
    ///
    /// ### Return Values
    ///
    /// - `result`: `Ok(())` on success, `ErrorCode` on error.
    /// - `key`: The key buffer.
    /// - `value`: The value buffer.
    fn update_complete(
        &self,
        result: Result<(), ErrorCode>,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    );

    /// This callback is called when the delete operation completes.
    ///
    /// ### Return Values
    ///
    /// - `result`: `Ok(())` on success, `ErrorCode` on error.
    /// - `key`: The key buffer.
    fn delete_complete(&self, result: Result<(), ErrorCode>, key: SubSliceMut<'static, u8>);
}

/// Key-Value interface with permissions.
///
/// This interface provides access to key-value storage where access control.
/// Each object is marked with a `write_id` (based on the `StoragePermissions`
/// used to create it), and all further accesses and modifications to that
/// object require suitable permissions.
pub trait KVPermissions<'a> {
    /// Configure the client for operation callbacks.
    fn set_client(&self, client: &'a dyn KVClient);

    /// Retrieve a value based on the given key.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: Where the returned value buffer will be stored.
    /// - `permissions`: The read/write/modify permissions for this access.
    ///
    /// ### Return
    ///
    /// - On success returns `Ok(())`. A callback will be issued.
    /// - On error, returns the buffers and:
    ///   - `ENOSUPPORT`: The key could not be found.
    ///   - `SIZE`: The value is longer than the provided buffer. The amount of
    ///     the value that fits in the buffer will be provided.
    fn get(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
        permissions: StoragePermissions,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Store a value based on the given key. If the key does not exist it will
    /// be added. If the key already exists the value will be updated.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store. The provided buffer MUST start
    ///   `KVPermissions.header_size()` bytes after the beginning of the buffer
    ///   to enable the implementation to insert a header.
    /// - `permissions`: The read/write/modify permissions for this access.
    fn set(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
        permissions: StoragePermissions,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Store a new value based on the given key. If the key does not exist it
    /// will be added. If the key already exists an error callback will be
    /// provided.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store. The provided buffer MUST start
    ///   `KVPermissions.header_size()` bytes after the beginning of the buffer
    ///   to enable the implementation to insert a header.
    /// - `permissions`: The read/write/modify permissions for this access.
    fn add(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
        permissions: StoragePermissions,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Modify a value based on the given key. If the key does not exist it an
    /// error callback will be provided.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store. The provided buffer MUST start
    ///   `KVPermissions.header_size()` bytes after the beginning of the buffer
    ///   to enable the implementation to insert a header.
    /// - `permissions`: The read/write/modify permissions for this access.
    fn update(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
        permissions: StoragePermissions,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Delete a key-value object based on the given key.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `permissions`: The read/write/modify permissions for this access.
    fn delete(
        &self,
        key: SubSliceMut<'static, u8>,
        permissions: StoragePermissions,
    ) -> Result<(), (SubSliceMut<'static, u8>, ErrorCode)>;

    /// Returns the length of the key-value store's header in bytes.
    ///
    /// Room for this header must be accommodated in a `set`, `add`, or `update`
    /// operation.
    fn header_size(&self) -> usize;
}

/// Key-Value interface.
///
/// This interface provides access to key-value storage where access control.
/// Each object is marked with a `write_id` (based on the `StoragePermissions`
/// used to create it), and all further accesses and modifications to that
/// object require suitable permissions.
pub trait KV<'a> {
    /// Configure the client for operation callbacks.
    fn set_client(&self, client: &'a dyn KVClient);

    /// Retrieve a value based on the given key.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: Where the returned value buffer will be stored.
    ///
    /// ### Return
    ///
    /// - On success returns `Ok(())`. A callback will be issued.
    /// - On error, returns the buffers and:
    ///   - `ENOSUPPORT`: The key could not be found.
    ///   - `SIZE`: The value is longer than the provided buffer. The amount of
    ///     the value that fits in the buffer will be provided.
    fn get(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Store a value based on the given key. If the key does not exist it will
    /// be added. If the key already exists the value will be updated.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store.
    fn set(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Store a new value based on the given key. If the key does not exist it
    /// will be added. If the key already exists an error callback will be
    /// provided.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store.
    fn add(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Modify a value based on the given key. If the key does not exist it an
    /// error callback will be provided.
    ///
    /// The `value` buffer must have room for a header.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    /// - `value`: The value to store.
    fn update(
        &self,
        key: SubSliceMut<'static, u8>,
        value: SubSliceMut<'static, u8>,
    ) -> Result<
        (),
        (
            SubSliceMut<'static, u8>,
            SubSliceMut<'static, u8>,
            ErrorCode,
        ),
    >;

    /// Delete a key-value object based on the given key.
    ///
    /// ### Arguments
    ///
    /// - `key`: The key to identify the k-v pair.
    fn delete(
        &self,
        key: SubSliceMut<'static, u8>,
    ) -> Result<(), (SubSliceMut<'static, u8>, ErrorCode)>;
}
