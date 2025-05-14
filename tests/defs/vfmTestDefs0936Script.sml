open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0936";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallValueCheck.json";
val defs = mapi (define_test "0936") tests;
val () = export_theory_no_docs ();
