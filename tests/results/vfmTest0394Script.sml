open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0394Theory;
val () = new_theory "vfmTest0394";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0394") $ get_result_defs "vfmTestDefs0394";
val () = export_theory_no_docs ();
