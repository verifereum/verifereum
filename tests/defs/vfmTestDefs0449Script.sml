Theory vfmTestDefs0449[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/lt.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/lt.json");
val defs = mapi (define_test "0449") tests;
