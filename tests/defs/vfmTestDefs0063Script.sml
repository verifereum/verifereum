Theory vfmTestDefs0063[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/calldata_lengths.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/calldata_lengths.json");
val defs = mapi (define_test "0063") tests;
