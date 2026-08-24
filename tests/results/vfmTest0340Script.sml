Theory vfmTest0340[no_sig_docs]
Ancestors vfmTestDefs0340
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0340_0.nsv"];
val thyn = "vfmTestDefs0340";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
