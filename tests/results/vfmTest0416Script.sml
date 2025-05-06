open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0416Theory;
val () = new_theory "vfmTest0416";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0416") $ get_result_defs "vfmTestDefs0416";
val () = export_theory_no_docs ();
