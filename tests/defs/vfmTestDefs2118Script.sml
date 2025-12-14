open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2118";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallContractToCreateContractAndCallItOOG.json";
val defs = mapi (define_test "2118") tests;
val () = export_theory_no_docs ();
