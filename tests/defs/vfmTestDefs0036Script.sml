Theory vfmTestDefs0036[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_calldata_lengths.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4788_beacon_root/test_calldata_lengths.json");
val defs = mapi (define_test "0036") tests;
