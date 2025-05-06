open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2320Theory;
val () = new_theory "vfmTest2320";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2320") $ get_result_defs "vfmTestDefs2320";
val () = export_theory_no_docs ();
