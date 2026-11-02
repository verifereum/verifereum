Theory vfmTestDefs0928[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_contract_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_contract_calls.json");
val defs = mapi (define_test "0928") tests;
