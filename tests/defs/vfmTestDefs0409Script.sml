Theory vfmTestDefs0409[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP4844_blobtransactions/emptyBlobhashList.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP4844_blobtransactions/emptyBlobhashList.json");
val defs = mapi (define_test "0409") tests;
