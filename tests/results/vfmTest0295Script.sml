open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0295Theory;
val () = new_theory "vfmTest0295";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0295") $ get_result_defs "vfmTestDefs0295";
val () = export_theory_no_docs ();
