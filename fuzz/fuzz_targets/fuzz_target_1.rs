#![no_main]
use libfuzzer_sys::fuzz_target;

use stack_map::StackMap;

fn prop<const FANOUT: usize>(data: &[u64]) {
    let mut sm = StackMap::<u64, u64, FANOUT>::default();
    let mut model = std::collections::BTreeMap::<u64, u64>::default();
    for item in data {
        let ret_1 = sm.insert(*item, *item);
        let ret_2 = model.insert(*item, *item);

        assert_eq!(ret_1, ret_2);

        if sm.is_full() {
            break;
        }
    }

    let sm_iter: Vec<_> = sm.iter().map(|(k, v)| (*k, *v)).collect();
    let model_iter: Vec<_> = model.iter().map(|(k, v)| (*k, *v)).collect();

    assert_eq!(sm_iter, model_iter);

    let serialized = bincode::serialize(&sm).unwrap();
    let deserialized: StackMap<u64, u64, FANOUT> = bincode::deserialize(&serialized).unwrap();
    assert_eq!(deserialized, sm);
}

fuzz_target!(|data: Vec<u64>| {
    prop::<1>(&data);
    prop::<2>(&data);
    prop::<3>(&data);
    prop::<4>(&data);
    prop::<5>(&data);
    prop::<7>(&data);
    prop::<8>(&data);
    prop::<9>(&data);
    prop::<11>(&data);
    prop::<15>(&data);
    prop::<16>(&data);
    prop::<17>(&data);
    prop::<21>(&data);
    prop::<24>(&data);
    prop::<32>(&data);
    prop::<43>(&data);
    prop::<50>(&data);
    prop::<64>(&data);
    prop::<87>(&data);
    prop::<100>(&data);
    prop::<128>(&data);
});
