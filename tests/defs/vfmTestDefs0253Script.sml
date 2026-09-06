Theory vfmTestDefs0253[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7883_modexp_gas_increase/eip_mainnet/modexp_different_base_lengths.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7883_modexp_gas_increase/eip_mainnet/modexp_different_base_lengths.json");
val defs = mapi (define_test "0253") tests;
