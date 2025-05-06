open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0968Theory;
val () = new_theory "vfmTest0968";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0968") $ get_result_defs "vfmTestDefs0968";
val () = export_theory_no_docs ();
