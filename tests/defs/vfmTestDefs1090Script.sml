Theory vfmTestDefs1090[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/precompiles/precompile_absence/precompile_absence.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/precompiles/precompile_absence/precompile_absence.json");
val defs = mapi (define_test "1090") tests;
