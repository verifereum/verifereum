open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1943Theory;
val () = new_theory "vfmTest1943";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1943") $ get_result_defs "vfmTestDefs1943";
val () = export_theory_no_docs ();
