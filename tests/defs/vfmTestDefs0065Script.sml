Theory vfmTestDefs0065[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/multi_block_beacon_root_timestamp_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/multi_block_beacon_root_timestamp_calls.json");
val defs = mapi (define_test "0065") tests;
