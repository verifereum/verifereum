Theory vfmTestDefs0024[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/ecpairing_fuzzed/invalid_g2_subgroup.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/ecpairing_fuzzed/invalid_g2_subgroup.json");
val defs = mapi (define_test "0024") tests;
