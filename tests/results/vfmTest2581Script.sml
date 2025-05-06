open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2581Theory;
val () = new_theory "vfmTest2581";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2581") $ get_result_defs "vfmTestDefs2581";
val () = export_theory_no_docs ();
