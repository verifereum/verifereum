open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0554Theory;
val () = new_theory "vfmTest0554";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0554") $ get_result_defs "vfmTestDefs0554";
val () = export_theory_no_docs ();
