Theory vfmTestDefs0406[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/transStorageOK.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/transStorageOK.json");
val defs = mapi (define_test "0406") tests;
