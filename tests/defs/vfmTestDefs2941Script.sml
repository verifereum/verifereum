Theory vfmTestDefs2941[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/vmArithmeticTest/two_ops/two_ops.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/vmArithmeticTest/two_ops/two_ops.json");
val defs = mapi (define_test "2941") tests;
