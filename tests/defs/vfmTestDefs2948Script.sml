Theory vfmTestDefs2948[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/vmBitwiseLogicOperation/not/not.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/vmBitwiseLogicOperation/not/not.json");
val defs = mapi (define_test "2948") tests;
