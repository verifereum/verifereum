Theory vfmTestDefs1158[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemoryTest/extcodecopy_dejavu.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemoryTest/extcodecopy_dejavu.json");
val defs = mapi (define_test "1158") tests;
