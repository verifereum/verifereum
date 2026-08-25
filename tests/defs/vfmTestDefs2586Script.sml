Theory vfmTestDefs2586[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_340282366920938463463374607431768211456_21000_128.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_340282366920938463463374607431768211456_21000_128.json");
val defs = mapi (define_test "2586") tests;
