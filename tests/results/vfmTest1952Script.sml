open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1952Theory;
val () = new_theory "vfmTest1952";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1952") $ get_result_defs "vfmTestDefs1952";
val () = export_theory_no_docs ();
