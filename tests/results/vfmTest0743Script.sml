open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0743Theory;
val () = new_theory "vfmTest0743";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0743") $ get_result_defs "vfmTestDefs0743";
val () = export_theory_no_docs ();
