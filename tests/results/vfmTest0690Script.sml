open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0690Theory;
val () = new_theory "vfmTest0690";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0690") $ get_result_defs "vfmTestDefs0690";
val () = export_theory_no_docs ();
