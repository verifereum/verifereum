Theory vfmTestDefs0354[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stBugs/returndatacopy_python_bug_tue_03_48_41_minus_1432/returndatacopy_python_bug_tue_03_48_41_minus_1432.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stBugs/returndatacopy_python_bug_tue_03_48_41_minus_1432/returndatacopy_python_bug_tue_03_48_41_minus_1432.json");
val defs = mapi (define_test "0354") tests;
