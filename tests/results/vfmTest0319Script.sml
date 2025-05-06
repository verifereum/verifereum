open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0319Theory;
val () = new_theory "vfmTest0319";
val thyn = "vfmTestDefs0319";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
