Theory vfmTestDefs1930[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRevertTest/PythonRevertTestTue201814-1430.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRevertTest/PythonRevertTestTue201814-1430.json");
val defs = mapi (define_test "1930") tests;
