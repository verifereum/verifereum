Theory vfmTestDefs1449[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP150Specific/transaction64_rule/transaction64_rule.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP150Specific/transaction64_rule/transaction64_rule.json");
val defs = mapi (define_test "1449") tests;
