Theory vfmTestDefs2775[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_340282366920938463463374607431768211456_21000_80.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_340282366920938463463374607431768211456_21000_80.json");
val defs = mapi (define_test "2775") tests;
