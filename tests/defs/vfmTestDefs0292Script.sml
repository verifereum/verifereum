open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0292";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/initcode/contract_creating_tx.json";
val defs = mapi (define_test "0292") tests;
val () = export_theory_no_docs ();
