Theory vfmTestDefs2626[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_340282366920938463463374607431768211456_21000_96.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_340282366920938463463374607431768211456_21000_96.json");
val defs = mapi (define_test "2626") tests;
