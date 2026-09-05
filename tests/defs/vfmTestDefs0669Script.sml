Theory vfmTestDefs0669[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_results/returndatacopy_after_successful_create_aborts.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_results/returndatacopy_after_successful_create_aborts.json");
val defs = mapi (define_test "0669") tests;
