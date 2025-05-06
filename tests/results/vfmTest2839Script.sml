open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2839Theory;
val () = new_theory "vfmTest2839";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2839") $ get_result_defs "vfmTestDefs2839";
val () = export_theory_no_docs ();
