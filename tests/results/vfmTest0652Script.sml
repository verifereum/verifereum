Theory vfmTest0652[no_sig_docs]
Ancestors vfmTestDefs0652
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0652_0.nsv", "result0652_1.nsv"];
val thyn = "vfmTestDefs0652";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
