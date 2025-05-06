open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0485Theory;
val () = new_theory "vfmTest0485";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0485") $ get_result_defs "vfmTestDefs0485";
val () = export_theory_no_docs ();
