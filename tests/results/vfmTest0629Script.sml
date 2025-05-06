open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0629Theory;
val () = new_theory "vfmTest0629";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0629") $ get_result_defs "vfmTestDefs0629";
val () = export_theory_no_docs ();
