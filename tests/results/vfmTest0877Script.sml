open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0877Theory;
val () = new_theory "vfmTest0877";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0877") $ get_result_defs "vfmTestDefs0877";
val () = export_theory_no_docs ();
