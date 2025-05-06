open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0661Theory;
val () = new_theory "vfmTest0661";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0661") $ get_result_defs "vfmTestDefs0661";
val () = export_theory_no_docs ();
