open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1350Theory;
val () = new_theory "vfmTest1350";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1350") $ get_result_defs "vfmTestDefs1350";
val () = export_theory_no_docs ();
