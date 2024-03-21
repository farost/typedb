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

use std::{
    cell::OnceCell, fs, ops::Deref, path::{Path, PathBuf}, sync::Mutex
};

use logger::initialise_logging;
use tracing::subscriber::DefaultGuard;

pub static LOGGING_GUARD: Mutex<OnceCell<DefaultGuard>> = Mutex::new(OnceCell::new());

pub fn init_logging() {
    LOGGING_GUARD.lock().unwrap().get_or_init(initialise_logging);
}

pub struct TempDir(PathBuf);

impl Drop for TempDir {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).ok();
    }
}

impl Deref for TempDir {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn create_tmp_dir() -> TempDir {
    let id = rand::random::<u64>();
    let dir_name = format!("test_storage_{}", id);
    let dir = std::env::temp_dir().join(Path::new(&dir_name));
    fs::create_dir_all(&dir).unwrap();
    TempDir(dir)
}
