open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0290";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3855_push0/push0/push0_contract_during_call_contexts.json";
val defs = mapi (define_test "0290") tests;
val () = export_theory_no_docs ();
