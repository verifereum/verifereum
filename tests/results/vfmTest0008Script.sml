open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0008Theory;
val () = new_theory "vfmTest0008";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0008") $ get_result_defs "vfmTestDefs0008";
val () = export_theory_no_docs ();
