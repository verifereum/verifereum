Theory vfmTestDefs2050[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSolidityTest/RecursiveCreateContractsCreate4Contracts.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSolidityTest/RecursiveCreateContractsCreate4Contracts.json");
val defs = mapi (define_test "2050") tests;
