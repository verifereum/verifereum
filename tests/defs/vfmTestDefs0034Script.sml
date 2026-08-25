Theory vfmTestDefs0034[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_selfdestruct.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_selfdestruct.json");
val defs = mapi (define_test "0034") tests;
