Theory vfmTestDefs1632[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRevertTest/python_revert_test_tue201814_minus_1430/python_revert_test_tue201814_minus_1430.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRevertTest/python_revert_test_tue201814_minus_1430/python_revert_test_tue201814_minus_1430.json");
val defs = mapi (define_test "1632") tests;
