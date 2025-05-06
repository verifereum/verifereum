open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0367Theory;
val () = new_theory "vfmTest0367";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0367") $ get_result_defs "vfmTestDefs0367";
val () = export_theory_no_docs ();
