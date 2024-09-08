/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{
    error::Error,
    fmt::{Display, Formatter},
};

use answer::variable::Variable;
use ir::pattern::constraint::Isa;
use itertools::Itertools;

use crate::insert::{ThingSource, TypeSource};

pub mod instructions;
pub mod program;
