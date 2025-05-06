open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2459Theory;
val () = new_theory "vfmTest2459";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2459") $ get_result_defs "vfmTestDefs2459";
val () = export_theory_no_docs ();
