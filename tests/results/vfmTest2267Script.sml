open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2267Theory;
val () = new_theory "vfmTest2267";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2267") $ get_result_defs "vfmTestDefs2267";
val () = export_theory_no_docs ();
