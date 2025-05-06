open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0281Theory;
val () = new_theory "vfmTest0281";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0281") $ get_result_defs "vfmTestDefs0281";
val () = export_theory_no_docs ();
