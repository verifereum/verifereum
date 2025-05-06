open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0398Theory;
val () = new_theory "vfmTest0398";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0398") $ get_result_defs "vfmTestDefs0398";
val () = export_theory_no_docs ();
