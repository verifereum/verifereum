Theory vfmTestDefs0060[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_contract_timestamps.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_contract_timestamps.json");
val defs = mapi (define_test "0060") tests;
