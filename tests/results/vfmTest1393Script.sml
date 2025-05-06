open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1393Theory;
val () = new_theory "vfmTest1393";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1393") $ get_result_defs "vfmTestDefs1393";
val () = export_theory_no_docs ();
