Theory vfmTestDefs0035[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_transition.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_transition.json");
val defs = mapi (define_test "0035") tests;
