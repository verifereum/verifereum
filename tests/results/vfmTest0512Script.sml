open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0512Theory;
val () = new_theory "vfmTest0512";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0512") $ get_result_defs "vfmTestDefs0512";
val () = export_theory_no_docs ();
