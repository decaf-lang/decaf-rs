pub mod loc;
pub mod errors;
pub mod ignore_result;
pub mod indent_printer;
pub mod r#ref;
pub mod op;

pub use crate::{loc::*, errors::*, ignore_result::*, indent_printer::*, r#ref::*, op::*};
use hashbrown::hash_map::DefaultHashBuilder;

pub const MAIN_CLASS: &str = "Main";
pub const MAIN_METHOD: &str = "main";
pub const LENGTH: &str = "length";
const INDENT: u32 = 4;
const INDENT_STR: &str = "    ";

// DefaultHashBuilder is the default hash of hashbrown, seems faster than RandomState (the default hash of IndexMap/Set & std HashMap/Set)
// place these type alias here just for convenience
pub type IndexMap<K, V> = indexmap::IndexMap<K, V, DefaultHashBuilder>;
pub type IndexSet<K> = indexmap::IndexSet<K, DefaultHashBuilder>;
pub type HashMap<K, V> = hashbrown::HashMap<K, V>;
pub type HashSet<K> = hashbrown::HashSet<K>;