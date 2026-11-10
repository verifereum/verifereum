Theory vfmTestDefs1406[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_results/create_results_with_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreateTest/create_results/create_results_with_call.json");
val defs = mapi (define_test "1406") tests;
