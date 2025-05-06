open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2612Theory;
val () = new_theory "vfmTest2612";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2612") $ get_result_defs "vfmTestDefs2612";
val () = export_theory_no_docs ();
