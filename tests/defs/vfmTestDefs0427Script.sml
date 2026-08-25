Theory vfmTestDefs0427[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/arith.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/arith.json");
val defs = mapi (define_test "0427") tests;
