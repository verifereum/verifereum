open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0495Theory;
val () = new_theory "vfmTest0495";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0495") $ get_result_defs "vfmTestDefs0495";
val () = export_theory_no_docs ();
