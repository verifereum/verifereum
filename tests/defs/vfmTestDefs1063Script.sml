Theory vfmTestDefs1063[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_nonEmptyMem_logMemSize1_logMemStart31.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stLogTests/log0_nonEmptyMem_logMemSize1_logMemStart31.json");
val defs = mapi (define_test "1063") tests;
