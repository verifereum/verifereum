open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2796Theory;
val () = new_theory "vfmTest2796";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2796") $ get_result_defs "vfmTestDefs2796";
val () = export_theory_no_docs ();
