open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0509Theory;
val () = new_theory "vfmTest0509";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0509") $ get_result_defs "vfmTestDefs0509";
val () = export_theory_no_docs ();
