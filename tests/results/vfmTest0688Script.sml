Theory vfmTest0688[no_sig_docs]
Ancestors vfmTestDefs0688
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0688_0.nsv"];
val thyn = "vfmTestDefs0688";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
