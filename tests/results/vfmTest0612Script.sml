open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0612Theory;
val () = new_theory "vfmTest0612";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0612") $ get_result_defs "vfmTestDefs0612";
val () = export_theory_no_docs ();
