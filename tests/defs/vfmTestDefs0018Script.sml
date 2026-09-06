Theory vfmTestDefs0018[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/ecpairing/fail.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip197_ec_pairing/ecpairing/fail.json");
val defs = mapi (define_test "0018") tests;
