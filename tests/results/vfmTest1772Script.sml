open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1772Theory;
val () = new_theory "vfmTest1772";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1772") $ get_result_defs "vfmTestDefs1772";
val () = export_theory_no_docs ();
