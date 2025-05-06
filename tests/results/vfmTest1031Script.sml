open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1031Theory;
val () = new_theory "vfmTest1031";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1031") $ get_result_defs "vfmTestDefs1031";
val () = export_theory_no_docs ();
