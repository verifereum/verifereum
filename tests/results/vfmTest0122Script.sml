open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0122Theory;
val () = new_theory "vfmTest0122";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0122") $ get_result_defs "vfmTestDefs0122";
val () = export_theory_no_docs ();
