open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0992Theory;
val () = new_theory "vfmTest0992";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0992") $ get_result_defs "vfmTestDefs0992";
val () = export_theory_no_docs ();
