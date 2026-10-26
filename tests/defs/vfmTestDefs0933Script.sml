Theory vfmTestDefs0933[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/invalid_beacon_root_calldata_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/invalid_beacon_root_calldata_value.json");
val defs = mapi (define_test "0933") tests;
