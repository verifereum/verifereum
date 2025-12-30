Theory vfmTestDefs0535[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/returndatacopyPythonBug_Tue_03_48_41-1432.json";
val defs = mapi (define_test "0535") tests;
