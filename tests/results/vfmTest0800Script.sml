Theory vfmTest0800[no_sig_docs]
Ancestors vfmTestDefs0800
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0800_0.nsv"];
val thyn = "vfmTestDefs0800";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
