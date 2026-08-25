Theory vfmTestDefs0649[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailUndefinedInstruction2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailUndefinedInstruction2.json");
val defs = mapi (define_test "0649") tests;
