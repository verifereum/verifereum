open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0332Theory;
val () = new_theory "vfmTest0332";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0332") $ get_result_defs "vfmTestDefs0332";
val () = export_theory_no_docs ();
