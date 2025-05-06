open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2629Theory;
val () = new_theory "vfmTest2629";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2629") $ get_result_defs "vfmTestDefs2629";
val () = export_theory_no_docs ();
