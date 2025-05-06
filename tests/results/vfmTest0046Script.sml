open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0046Theory;
val () = new_theory "vfmTest0046";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0046") $ get_result_defs "vfmTestDefs0046";
val () = export_theory_no_docs ();
