use std::marker::PhantomData;

use serde::de::{Deserializer, MapAccess, Visitor};
use serde::{Deserialize, Serialize, Serializer};

use crate::StackMap;

impl<K, V, const FANOUT: usize> Serialize for StackMap<K, V, FANOUT>
where
    K: Serialize + Ord,
    V: Serialize,
{
    fn serialize<S>(&self, s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        use serde::ser::SerializeMap;
        let mut map = s.serialize_map(Some(self.len()))?;
        //let mut map = s.serialize_map(None)?;
        for (k, v) in self.iter() {
            map.serialize_entry(&k, &v)?;
        }
        map.end()
    }
}

struct StackMapVisitor<K, V, const FANOUT: usize> {
    pd: PhantomData<(K, V)>,
}

impl<'de, K, V, const FANOUT: usize> Visitor<'de> for StackMapVisitor<K, V, FANOUT>
where
    K: Deserialize<'de> + Ord,
    V: Deserialize<'de>,
{
    type Value = StackMap<K, V, FANOUT>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a StackMap<K, V, FANOUT>")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        use serde::de::Error;
        let mut map = StackMap::default();

        while let Some((key, value)) = access.next_entry()? {
            if map.is_full() {
                return Err(M::Error::custom(format!(
                    "StackMap with FANOUT (maximum capacity) of {} is too small to be deserialized from this \
                    data, which contains more data than would fit in the fixed size container",
                    FANOUT
                )));
            }
            map.insert(key, value);
        }

        Ok(map)
    }
}

impl<'de, K, V, const FANOUT: usize> Deserialize<'de> for StackMap<K, V, FANOUT>
where
    K: Deserialize<'de> + Ord,
    V: Deserialize<'de>,
{
    fn deserialize<D>(d: D) -> Result<StackMap<K, V, FANOUT>, D::Error>
    where
        D: Deserializer<'de>,
    {
        d.deserialize_map(StackMapVisitor { pd: PhantomData })
    }
}
