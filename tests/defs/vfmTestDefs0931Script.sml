Theory vfmTestDefs0931[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_selfdestruct.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_selfdestruct.json");
val defs = mapi (define_test "0931") tests;
