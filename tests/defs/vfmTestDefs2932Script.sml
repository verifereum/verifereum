Theory vfmTestDefs2932[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/vmArithmeticTest/fib/fib.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/vmArithmeticTest/fib/fib.json");
val defs = mapi (define_test "2932") tests;
