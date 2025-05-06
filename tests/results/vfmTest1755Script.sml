open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1755Theory;
val () = new_theory "vfmTest1755";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1755") $ get_result_defs "vfmTestDefs1755";
val () = export_theory_no_docs ();
