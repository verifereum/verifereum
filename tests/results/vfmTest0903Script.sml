Theory vfmTest0903[no_sig_docs]
Ancestors vfmTestDefs0903
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0903_0.nsv"];
val thyn = "vfmTestDefs0903";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
