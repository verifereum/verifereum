open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2905Theory;
val () = new_theory "vfmTest2905";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2905") $ get_result_defs "vfmTestDefs2905";
val () = export_theory_no_docs ();
