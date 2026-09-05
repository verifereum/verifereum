Theory vfmTestDefs2216[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroKnowledge/pairing_test/pairing_test.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroKnowledge/pairing_test/pairing_test.json");
val defs = mapi (define_test "2216") tests;
