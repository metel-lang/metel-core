use super::*;

#[test]
fn round_trips_known_paths() {
    for key in NativeKey::ALL {
        let id = key.surface_id().trim_start_matches('@');
        let path: Vec<String> = id.split('.').map(str::to_string).collect();
        assert_eq!(NativeKey::from_path(&path), Some(*key), "for {id}");
    }
}

#[test]
fn unknown_path_is_none() {
    assert_eq!(
        NativeKey::from_path(&["std".into(), "core".into(), "nope".into()]),
        None
    );
    assert_eq!(NativeKey::from_path(&["foo".into()]), None);
}
