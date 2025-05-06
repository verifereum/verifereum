open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0480Theory;
val () = new_theory "vfmTest0480";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0480") $ get_result_defs "vfmTestDefs0480";
val () = export_theory_no_docs ();
