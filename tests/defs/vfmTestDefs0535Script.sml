Theory vfmTestDefs0535[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stBugs/returndatacopyPythonBug_Tue_03_48_41-1432.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stBugs/returndatacopyPythonBug_Tue_03_48_41-1432.json");
val defs = mapi (define_test "0535") tests;
