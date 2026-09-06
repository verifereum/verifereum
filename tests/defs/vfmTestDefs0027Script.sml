Theory vfmTestDefs0027[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/gas/gas_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/gas/gas_costs.json");
val defs = mapi (define_test "0027") tests;
