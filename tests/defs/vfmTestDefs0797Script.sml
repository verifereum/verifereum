Theory vfmTestDefs0797[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_recursive_contract/call_recursive_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stInitCodeTest/call_recursive_contract/call_recursive_contract.json");
val defs = mapi (define_test "0797") tests;
