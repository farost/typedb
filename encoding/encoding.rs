/*
 * Copyright (C) 2023 Vaticle
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::error::Error;
use std::fmt::{Display, Formatter};
use std::str::Utf8Error;

use storage::{StorageSection, MVCCStorage};
use storage::error::MVCCStorageError;
pub use storage::key_value::{FIXED_KEY_LENGTH_BYTES, StorageKeyReference, StorageKeyReference};
use storage::key_value::{KeyspaceKeyDynamic, StorageValue};
use struct_deser::{FromBytes, IntoBytes, SerializedByteLen};

pub mod thing;
pub mod type_;
pub mod prefix;
pub mod label;
mod infix;
mod value;


enum EncodingSection {
    Schema,
    Data, // TODO: partition into sub-spaces for write optimisation
}

impl EncodingSection {
    const fn name(&self) -> &str {
        match self {
            EncodingSection::Schema => "schema",
            EncodingSection::Data => "data",
        }
    }

    const fn id(&self) -> u8 {
        match self {
            EncodingSection::Schema => 0b0,
            EncodingSection::Data => 0b100,
        }
    }

    fn initialise_storage(&self, storage: &mut MVCCStorage) -> Result<(), MVCCStorageError> {
        let options = MVCCStorage::new_db_options();
        storage.create_keyspace(self.name(), self.id(), &options)
    }
}

pub fn initialise_storage(storage: &mut MVCCStorage) -> Result<(), MVCCStorageError> {
    EncodingSection::Schema.initialise_storage(storage)?;
    EncodingSection::Data.initialise_storage(storage)
}

pub trait Serialisable {
    fn serialised_size(&self) -> usize;

    fn serialise_into(&self, array: &mut [u8]);
}

pub trait DeserialisableFixed {
    fn serialised_size() -> usize;

    fn deserialise_from(array: &[u8]) -> Self;
}

pub trait DeserialisableDynamic {
    fn deserialise_from(array: Box<[u8]>) -> Self;
}

impl<T: IntoBytes> Serialisable for T {
    fn serialised_size(&self) -> usize {
        Self::BYTE_LEN
    }

    fn serialise_into(&self, array: &mut [u8]) {
        debug_assert_eq!(array.len(), self.serialised_size());
        self.into_bytes(array)
    }
}

impl<T: FromBytes> DeserialisableFixed for T {
    fn serialised_size() -> usize {
        Self::BYTE_LEN
    }

    fn deserialise_from(array: &[u8]) -> Self {
        debug_assert_eq!(array.len(), Self::serialised_size());
        T::from_bytes(array)
    }
}

pub trait SerialisableKeyFixed: Serialisable {
    fn key_section_id(&self) -> u8;

    fn serialise_to_key(&self) -> StorageKeyReference {
        let mut bytes = vec![0; self.serialised_size()];
        self.serialise_into(bytes.as_mut_slice());
        StorageKeyReference::Dynamic(KeyspaceKeyDynamic::new(self.key_section_id(), bytes.into_boxed_slice()))
    }
}

pub trait SerialisableKeyDynamic: Serialisable {
    fn key_section_id(&self) -> u8;

    fn serialise_to_key(&self) -> StorageKeyReference {
        debug_assert!(self.serialised_size() < FIXED_KEY_LENGTH_BYTES);
        let mut data = [0; FIXED_KEY_LENGTH_BYTES];
        self.serialise_into(&mut data[0..self.serialised_size()]);
        StorageKeyReference::Fixed(StorageKeyReference::new(self.key_section_id(), self.serialised_size(), data))
    }
}

pub trait SerialisableValue: Serialisable {
    fn serialise_to_value(&self) -> StorageValue<'_, 48> {
        let mut bytes = vec![0; self.serialised_size()];
        self.serialise_into(bytes.as_mut_slice());
        StorageValue::Value(bytes.into_boxed_slice())
    }
}

// anything serialisable can be serialised as a value
impl<T: Serialisable> SerialisableValue for T {}

#[derive(Debug)]
pub struct EncodingError {
    pub kind: EncodingErrorKind,
}

#[derive(Debug)]
pub enum EncodingErrorKind {
    FailedUFT8Decode { bytes: Box<[u8]>, source: Utf8Error }
}

impl Display for EncodingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Error for EncodingError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            EncodingErrorKind::FailedUFT8Decode { source, .. } => Some(source),
        }
    }
}