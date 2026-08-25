Theory vfmTestDefs1206[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mload8bitBound.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryTest/mload8bitBound.json");
val defs = mapi (define_test "1206") tests;
