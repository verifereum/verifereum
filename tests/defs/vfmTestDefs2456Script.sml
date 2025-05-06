open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2456";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticFlagEnabled/DelegatecallToPrecompileFromCalledContract.json";
val defs = mapi (define_test "2456") tests;
val () = export_theory_no_docs ();
