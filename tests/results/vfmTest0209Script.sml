Theory vfmTest0209[no_sig_docs]
Ancestors vfmTestDefs0209
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0209_0.nsv"];
val thyn = "vfmTestDefs0209";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
