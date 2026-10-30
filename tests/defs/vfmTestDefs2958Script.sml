Theory vfmTestDefs2958[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/vmIOandFlowOperations/loops_conditionals/loops_conditionals.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/vmIOandFlowOperations/loops_conditionals/loops_conditionals.json");
val defs = mapi (define_test "2958") tests;
