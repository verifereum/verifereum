Theory vfmTest3103[no_sig_docs]
Ancestors vfmTestDefs3103
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3103_0.nsv"];
val thyn = "vfmTestDefs3103";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
