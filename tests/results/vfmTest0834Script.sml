Theory vfmTest0834[no_sig_docs]
Ancestors vfmTestDefs0834
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0834_0.nsv"];
val thyn = "vfmTestDefs0834";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
