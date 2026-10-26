Theory vfmTestDefs1110[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/istanbul/eip152_blake2/blake2/blake2b_invalid_input.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/istanbul/eip152_blake2/blake2/blake2b_invalid_input.json");
val defs = mapi (define_test "1110") tests;
