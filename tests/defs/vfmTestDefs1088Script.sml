Theory vfmTestDefs1088[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/precompiles/ecrecover/precompiles.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/precompiles/ecrecover/precompiles.json");
val defs = mapi (define_test "1088") tests;
