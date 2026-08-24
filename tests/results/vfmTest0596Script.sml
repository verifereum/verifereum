Theory vfmTest0596[no_sig_docs]
Ancestors vfmTestDefs0596
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0596_0.nsv"];
val thyn = "vfmTestDefs0596";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
