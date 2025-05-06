open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0893Theory;
val () = new_theory "vfmTest0893";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0893") $ get_result_defs "vfmTestDefs0893";
val () = export_theory_no_docs ();
