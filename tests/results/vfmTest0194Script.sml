open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0194Theory;
val () = new_theory "vfmTest0194";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0194") $ get_result_defs "vfmTestDefs0194";
val () = export_theory_no_docs ();
