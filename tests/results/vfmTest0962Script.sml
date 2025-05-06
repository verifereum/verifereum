open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0962Theory;
val () = new_theory "vfmTest0962";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0962") $ get_result_defs "vfmTestDefs0962";
val () = export_theory_no_docs ();
