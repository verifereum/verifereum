Theory vfmTestDefs0285[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7939_count_leading_zeros/eip_mainnet/clz_mainnet.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7939_count_leading_zeros/eip_mainnet/clz_mainnet.json");
val defs = mapi (define_test "0285") tests;
