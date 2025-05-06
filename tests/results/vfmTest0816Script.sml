open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0816Theory;
val () = new_theory "vfmTest0816";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0816") $ get_result_defs "vfmTestDefs0816";
val () = export_theory_no_docs ();
