Theory vfmTestDefs2330[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip6110_deposits/modified_contract/extra_logs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip6110_deposits/modified_contract/extra_logs.json");
val defs = mapi (define_test "2330") tests;
