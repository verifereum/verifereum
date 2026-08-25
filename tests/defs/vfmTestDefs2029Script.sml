Theory vfmTestDefs2029[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stShift/shl_-1_256.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stShift/shl_-1_256.json");
val defs = mapi (define_test "2029") tests;
