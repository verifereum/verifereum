open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2822Theory;
val () = new_theory "vfmTest2822";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2822") $ get_result_defs "vfmTestDefs2822";
val () = export_theory_no_docs ();
