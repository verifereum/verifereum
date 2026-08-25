Theory vfmTestDefs0146[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/precompiles/test_precompile_absence.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/precompiles/test_precompile_absence.json");
val defs = mapi (define_test "0146") tests;
