open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2772Theory;
val () = new_theory "vfmTest2772";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2772") $ get_result_defs "vfmTestDefs2772";
val () = export_theory_no_docs ();
