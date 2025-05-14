open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0937";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecodeDynamicCode.json";
val defs = mapi (define_test "0937") tests;
val () = export_theory_no_docs ();
