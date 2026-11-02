Theory vfmTestDefs2949[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/vmBitwiseLogicOperation/or/or.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/vmBitwiseLogicOperation/or/or.json");
val defs = mapi (define_test "2949") tests;
