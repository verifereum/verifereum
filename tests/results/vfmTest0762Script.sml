Theory vfmTest0762[no_sig_docs]
Ancestors vfmTestDefs0762
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0762_0.nsv"];
val thyn = "vfmTestDefs0762";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
